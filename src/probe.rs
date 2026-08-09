//! Generating vacuity probes.
//!
//! A postcondition is VACUOUS when it holds for every value its return type admits. Every
//! implementation then satisfies it, so proving it establishes nothing, and no reachability
//! analysis can detect that because nothing is unreachable.
//!
//! `Vacuity.lean` proves the check is one query:
//!
//! ```text
//! Vacuous I P  <->  forall g, TypeValid I g -> Satisfies P g
//! ```
//!
//! The right side quantifies over every implementation anyone could write. The left is a
//! single assertion over an unconstrained, type-valid return value. So this emits, per
//! clause, a harness that havocs the inputs AND the result and asserts the clause:
//!
//! ```rust,ignore
//! #[kani::proof]
//! fn probe_vacuity_count_ones_0() {
//!     let result: NonZero<u32> = kani::any();
//!     assert!(result.get() > 0);
//! }
//! ```
//!
//! VERIFICATION SUCCESS IS THE BUG REPORT. Failure is healthy: it produces a type-valid
//! value the clause rejects, proving the clause constrains something.
//!
//! WHY THIS DOMINATES WRITING MUTANTS.
//!   * A passing mutant set establishes nothing. This decides the question.
//!   * One query per clause, versus one build per mutant.
//!   * It never calls the function, so it works on clauses whose own harness cannot run.
//!     `Alignment::of` in the Rust standard library has its harness disabled behind
//!     kani#3905, and its clause was still decided this way.
//!
//! WHAT IS SKIPPED, AND WHY IT IS LISTED. A clause is only probeable when every type
//! involved can be produced by `kani::any()`. Generics, raw pointers, references and
//! unknown user types cannot, and each skip is REPORTED WITH ITS REASON. A generator that
//! silently emitted fewer probes than there are clauses would report a clean bill of
//! health for clauses it never examined.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use syn::{ImplItem, Item, TraitItem};

#[derive(Debug, Clone)]
pub struct Probe {
    pub file: PathBuf,
    pub line: usize,
    pub func: String,
    pub name: String,
    pub code: String,
}

#[derive(Debug, Clone)]
pub struct Skip {
    pub file: PathBuf,
    pub func: String,
    pub reason: String,
}

#[derive(Debug, Default)]
pub struct ProbeReport {
    pub clauses_seen: usize,
    pub probes: Vec<Probe>,
    pub skips: Vec<Skip>,
    /// Types found carrying a hand-written `impl kani::Arbitrary`, which makes them
    /// probeable even though they are not primitives.
    pub arbitrary_types: Vec<String>,
}

/// Types `kani::any()` can always produce.
const PRIMITIVE: &[&str] = &[
    "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
    "bool", "char", "NonZero", "Option", "Alignment",
    // Kani also derives Arbitrary for the NonZero* alias names, which head() sees
    // as distinct idents from the generic `NonZero`. Without these, real code using
    // `NonZeroU32`/`NonZeroUsize` (e.g. slitter) is skipped though it is probeable.
    "NonZeroU8", "NonZeroU16", "NonZeroU32", "NonZeroU64", "NonZeroU128", "NonZeroUsize",
    "NonZeroI8", "NonZeroI16", "NonZeroI32", "NonZeroI64", "NonZeroI128", "NonZeroIsize",
];

fn tokens(t: impl quote_lite::ToTokensLite) -> String {
    t.render()
}

mod quote_lite {
    use proc_macro2::TokenStream;
    use syn::__private::ToTokens;

    pub trait ToTokensLite {
        fn render(self) -> String;
    }
    impl<T: ToTokens> ToTokensLite for &T {
        fn render(self) -> String {
            let mut ts = TokenStream::new();
            self.to_tokens(&mut ts);
            ts.to_string()
        }
    }
}

/// The head identifier of a type: `NonZero` from `NonZero<u32>`, `u8` from `u8`.
fn head(ty: &syn::Type) -> Option<String> {
    match ty {
        syn::Type::Path(p) => p.path.segments.last().map(|s| s.ident.to_string()),
        _ => None,
    }
}

/// Can `kani::any::<ty>()` produce this? Every nested type argument must qualify too,
/// since `Option<*const u8>` is no more producible than `*const u8`.
fn probeable(ty: &syn::Type, known: &HashSet<String>) -> Result<(), String> {
    match ty {
        syn::Type::Path(p) => {
            let seg = p.path.segments.last().ok_or("empty type path")?;
            let name = seg.ident.to_string();
            if !PRIMITIVE.contains(&name.as_str()) && !known.contains(&name) {
                return Err(format!("`{name}` has no kani::Arbitrary this tool can see"));
            }
            if let syn::PathArguments::AngleBracketed(a) = &seg.arguments {
                for arg in &a.args {
                    if let syn::GenericArgument::Type(t) = arg {
                        probeable(t, known)?;
                    }
                }
            }
            Ok(())
        }
        syn::Type::Ptr(_) => Err("raw pointer, kani::any() cannot produce a valid one".into()),
        syn::Type::Reference(_) => Err("reference, needs a referent to point at".into()),
        syn::Type::Tuple(t) => {
            for e in &t.elems {
                probeable(e, known)?;
            }
            Ok(())
        }
        _ => Err(format!("unsupported type form `{}`", tokens(ty))),
    }
}

/// Rename a word without touching identifiers that merely contain it.
fn rename_word(src: &str, from: &str, to: &str) -> String {
    let mut out = String::with_capacity(src.len());
    let b = src.as_bytes();
    let mut i = 0;
    while i < b.len() {
        let c = b[i] as char;
        if c.is_alphanumeric() || c == '_' {
            let start = i;
            while i < b.len() && ((b[i] as char).is_alphanumeric() || b[i] == b'_') {
                i += 1;
            }
            let w = &src[start..i];
            out.push_str(if w == from { to } else { w });
        } else {
            out.push(c);
            i += 1;
        }
    }
    out
}

/// Collect `impl kani::Arbitrary for T` so hand-written instances count as probeable.
fn collect_arbitrary(items: &[Item], out: &mut HashSet<String>) {
    for it in items {
        match it {
            Item::Impl(i) => {
                let is_arb = i
                    .trait_
                    .as_ref()
                    .and_then(|(_, p, _)| p.segments.last())
                    .is_some_and(|s| s.ident == "Arbitrary");
                if is_arb {
                    if let Some(n) = head(&i.self_ty) {
                        out.insert(n);
                    }
                }
            }
            Item::Mod(m) => {
                if let Some((_, inner)) = &m.content {
                    collect_arbitrary(inner, out);
                }
            }
            _ => {}
        }
    }
}

struct Ctx<'a> {
    file: &'a Path,
    known: &'a HashSet<String>,
    rep: &'a mut ProbeReport,
    seq: usize,
    /// When true, probe PRECONDITIONS (are the #[requires] jointly satisfiable)
    /// instead of postconditions. Precondition vacuity is return-type-independent
    /// and is the `assume(false)` gap the Kani paper flags as manual review.
    precond: bool,
    /// When true, probe COMPLETENESS: does the postcondition accept a return value
    /// OTHER than the one the implementation produces? A satisfiable cover means the
    /// contract is loose (some wrong output survives it). This is the one-query
    /// decision form of mutation adequacy (POSTCONDBENCH-style completeness).
    completeness: bool,
}

fn ensures_clauses(attrs: &[syn::Attribute]) -> Vec<String> {
    attrs
        .iter()
        // Match both the bare `#[ensures(...)]` (verify-rust-std re-export) and
        // the fully-qualified `#[kani::ensures(...)]` (Kani's own contract form)
        // by keying on the path's final segment rather than the whole path.
        .filter(|a| a.path().segments.last().is_some_and(|s| s.ident == "ensures"))
        .filter_map(|a| match &a.meta {
            syn::Meta::List(l) => Some(l.tokens.to_string()),
            _ => None,
        })
        .collect()
}

/// Preconditions: `#[requires(...)]` / `#[kani::requires(...)]`. Unlike ensures,
/// the body is a bare boolean expression, not a `|result|` closure.
fn requires_clauses(attrs: &[syn::Attribute]) -> Vec<String> {
    attrs
        .iter()
        .filter(|a| a.path().segments.last().is_some_and(|s| s.ident == "requires"))
        .filter_map(|a| match &a.meta {
            syn::Meta::List(l) => Some(l.tokens.to_string()),
            _ => None,
        })
        .collect()
}

/// Emit one probe per contracted function that havocs the inputs, assumes every
/// precondition, then `kani::cover!(true)`. If that cover is UNREACHABLE the
/// preconditions are jointly unsatisfiable, so any proof under them is vacuous.
/// Return-type-independent: it never constructs or names the result.
fn build_precondition(
    attrs: &[syn::Attribute],
    sig: &syn::Signature,
    self_ty: Option<&syn::Type>,
    ctx: &mut Ctx,
) {
    let clauses = requires_clauses(attrs);
    if clauses.is_empty() {
        return;
    }
    let fname = sig.ident.to_string();
    ctx.rep.clauses_seen += clauses.len();
    let mut fail = |why: String, ctx: &mut Ctx| {
        ctx.rep.skips.push(Skip { file: ctx.file.to_path_buf(), func: fname.clone(), reason: why });
    };

    if sig.generics.params.iter().any(|p| matches!(p, syn::GenericParam::Type(_))) {
        fail("generic function, no type arguments to instantiate".into(), ctx);
        return;
    }

    // Havoc every input; a precondition constrains the inputs, so they must be free.
    let mut binds = Vec::new();
    for a in &sig.inputs {
        match a {
            syn::FnArg::Receiver(_) => {
                let Some(st) = self_ty else {
                    fail("takes self but is not in an impl block".into(), ctx);
                    return;
                };
                if let Err(e) = probeable(st, ctx.known) {
                    fail(format!("self type: {e}"), ctx);
                    return;
                }
                binds.push(format!("let probe_self: {} = kani::any();", tokens(st)));
            }
            syn::FnArg::Typed(t) => {
                if let Err(e) = probeable(&t.ty, ctx.known) {
                    fail(format!("parameter: {e}"), ctx);
                    return;
                }
                let syn::Pat::Ident(id) = &*t.pat else {
                    fail("parameter is a pattern, not a plain name".into(), ctx);
                    return;
                };
                binds.push(format!("let {}: {} = kani::any();", id.ident, tokens(&t.ty)));
            }
        }
    }

    // Turn each requires clause into an assume. The predicate is the first
    // comma-separated element (the contracts crate allows a trailing "message").
    // A clause using the contracts `->` implication is not valid Rust, so skip it.
    let mut assumes = Vec::new();
    for (i, raw) in clauses.iter().enumerate() {
        let pred = first_expr(raw);
        if syn::parse_str::<syn::Expr>(&pred).is_err() {
            fail(format!("clause {i} is not a bare Rust expression this tool can assume"), ctx);
            return;
        }
        let pred = rename_word(&pred, "self", "probe_self");
        assumes.push(format!("kani::assume({pred});"));
    }

    ctx.seq += 1;
    let name = format!("probe_precond_{}_{}", fname, ctx.seq);
    let code = format!(
        "    /// Probes `{fname}` preconditions. An UNREACHABLE cover means they are jointly\n\
         \x20   /// unsatisfiable, so every proof under them is VACUOUS.\n\
         \x20   #[kani::proof]\n\
         \x20   fn {name}() {{\n\
         \x20       {}\n        {}\n        kani::cover!(true, \"preconditions jointly satisfiable\");\n\
         \x20   }}\n",
        binds.join("\n        "),
        assumes.join("\n        "),
    );
    ctx.rep.probes.push(Probe {
        file: ctx.file.to_path_buf(),
        line: sig.ident.span().start().line,
        func: fname.clone(),
        name,
        code,
    });
}

/// The first comma-separated element of a token string, so `pred, "msg"` yields
/// `pred`. Respects nesting so a comma inside `f(a, b)` does not split.
fn first_expr(raw: &str) -> String {
    let (mut depth, mut end) = (0i32, raw.len());
    for (i, c) in raw.char_indices() {
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            ',' if depth == 0 => {
                end = i;
                break;
            }
            _ => {}
        }
    }
    raw[..end].trim().to_string()
}

fn build(
    attrs: &[syn::Attribute],
    sig: &syn::Signature,
    self_ty: Option<&syn::Type>,
    ctx: &mut Ctx,
) {
    if ctx.completeness {
        build_completeness(attrs, sig, self_ty, ctx);
        return;
    }
    if ctx.precond {
        build_precondition(attrs, sig, self_ty, ctx);
        return;
    }
    let clauses = ensures_clauses(attrs);
    if clauses.is_empty() {
        return;
    }
    let fname = sig.ident.to_string();
    ctx.rep.clauses_seen += clauses.len();

    let mut fail = |why: String, ctx: &mut Ctx| {
        ctx.rep.skips.push(Skip { file: ctx.file.to_path_buf(), func: fname.clone(), reason: why });
    };

    // A generic function cannot be instantiated without choosing type arguments, and
    // choosing for the author would probe a different function than the one written.
    if sig.generics.params.iter().any(|p| matches!(p, syn::GenericParam::Type(_))) {
        fail("generic function, no type arguments to instantiate".into(), ctx);
        return;
    }

    let ret = match &sig.output {
        // `Self` in a return position means the impl's type. Without this, every
        // constructor in an impl block is skipped as an unknown type.
        syn::ReturnType::Type(_, t) => match (head(t).as_deref(), self_ty) {
            (Some("Self"), Some(st)) => st.clone(),
            _ => (**t).clone(),
        },
        syn::ReturnType::Default => {
            fail("returns unit, so there is no result to constrain".into(), ctx);
            return;
        }
    };
    if let Err(e) = probeable(&ret, ctx.known) {
        fail(format!("return type: {e}"), ctx);
        return;
    }

    // Bindings for every input, because vacuity quantifies over inputs as well as results.
    let mut binds = Vec::new();
    for a in &sig.inputs {
        match a {
            syn::FnArg::Receiver(_) => {
                let Some(st) = self_ty else {
                    fail("takes self but is not in an impl block".into(), ctx);
                    return;
                };
                if let Err(e) = probeable(st, ctx.known) {
                    fail(format!("self type: {e}"), ctx);
                    return;
                }
                binds.push(format!("let probe_self: {} = kani::any();", tokens(st)));
            }
            syn::FnArg::Typed(t) => {
                if let Err(e) = probeable(&t.ty, ctx.known) {
                    fail(format!("parameter: {e}"), ctx);
                    return;
                }
                let syn::Pat::Ident(id) = &*t.pat else {
                    fail("parameter is a pattern, not a plain name".into(), ctx);
                    return;
                };
                binds.push(format!("let {}: {} = kani::any();", id.ident, tokens(&t.ty)));
            }
        }
    }

    for (i, raw) in clauses.iter().enumerate() {
        // `|result| EXPR` or `|result: &Self| EXPR`
        let Ok(closure) = syn::parse_str::<syn::ExprClosure>(raw) else {
            fail(format!("clause {i} is not a closure this tool can parse"), ctx);
            continue;
        };
        let Some(syn::Pat::Ident(bind)) = closure.inputs.first().map(strip_type) else {
            fail(format!("clause {i} has no simple result binding"), ctx);
            continue;
        };
        let body = rename_word(&tokens(&*closure.body), "self", "probe_self");
        let rname = bind.ident.to_string();

        // ALWAYS BY REFERENCE. Kani's `ensures` macro binds the result as `&T`, which is
        // why real clauses deref it (`|result| *result > 0` on `Alignment::mask`). Binding
        // by value makes those probes fail to compile. A reference works for both forms,
        // because `result.get()` auto-derefs through `&`.
        let result_bind = format!(
            "let probe_result: {} = kani::any();\n        let {rname} = &probe_result;",
            tokens(&ret)
        );

        ctx.seq += 1;
        let name = format!("probe_vacuity_{}_{}", fname, ctx.seq);
        let code = format!(
            "    /// Probes `{fname}` clause {i}. SUCCESS means the clause is VACUOUS.\n\
             \x20   #[kani::proof]\n\
             \x20   fn {name}() {{\n\
             \x20       {}\n        {result_bind}\n        assert!({body});\n\
             \x20   }}\n",
            binds.join("\n        ")
        );
        ctx.rep.probes.push(Probe {
            file: ctx.file.to_path_buf(),
            line: sig.ident.span().start().line,
            func: fname.clone(),
            name,
            code,
        });
    }
}

/// Completeness (one-query mutation adequacy): call the real function to get the
/// correct output, havoc a DIFFERENT output, and cover the postcondition on it.
/// A SATISFIED cover means a wrong output satisfies the contract, so some
/// output-changing implementation survives it and the contract is loose. An
/// UNREACHABLE cover means only the true output passes: the contract is tight.
/// Requires the return type to be probeable AND `PartialEq` (for `wrong != correct`).
fn build_completeness(
    attrs: &[syn::Attribute],
    sig: &syn::Signature,
    self_ty: Option<&syn::Type>,
    ctx: &mut Ctx,
) {
    let clauses = ensures_clauses(attrs);
    if clauses.is_empty() {
        return;
    }
    let fname = sig.ident.to_string();
    ctx.rep.clauses_seen += clauses.len();
    let mut fail = |why: String, ctx: &mut Ctx| {
        ctx.rep.skips.push(Skip { file: ctx.file.to_path_buf(), func: fname.clone(), reason: why });
    };
    if sig.generics.params.iter().any(|p| matches!(p, syn::GenericParam::Type(_))) {
        fail("generic function, no type arguments to instantiate".into(), ctx);
        return;
    }
    let ret = match &sig.output {
        syn::ReturnType::Type(_, t) => match (head(t).as_deref(), self_ty) {
            (Some("Self"), Some(st)) => st.clone(),
            _ => (**t).clone(),
        },
        syn::ReturnType::Default => {
            fail("returns unit, so there is no result to constrain".into(), ctx);
            return;
        }
    };
    if let Err(e) = probeable(&ret, ctx.known) {
        fail(format!("return type: {e}"), ctx);
        return;
    }

    let mut binds = Vec::new();
    let mut args: Vec<String> = Vec::new();
    let mut is_method = false;
    for a in &sig.inputs {
        match a {
            syn::FnArg::Receiver(_) => {
                let Some(st) = self_ty else {
                    fail("takes self but is not in an impl block".into(), ctx);
                    return;
                };
                if let Err(e) = probeable(st, ctx.known) {
                    fail(format!("self type: {e}"), ctx);
                    return;
                }
                binds.push(format!("let probe_self: {} = kani::any();", tokens(st)));
                is_method = true;
            }
            syn::FnArg::Typed(t) => {
                if let Err(e) = probeable(&t.ty, ctx.known) {
                    fail(format!("parameter: {e}"), ctx);
                    return;
                }
                let syn::Pat::Ident(id) = &*t.pat else {
                    fail("parameter is a pattern, not a plain name".into(), ctx);
                    return;
                };
                binds.push(format!("let {}: {} = kani::any();", id.ident, tokens(&t.ty)));
                args.push(id.ident.to_string());
            }
        }
    }

    // Conjunction of all ensures clauses, each with its result binding pointed at the
    // havoc'd wrong output.
    let mut result_binds = Vec::new();
    let mut bodies = Vec::new();
    for (i, raw) in clauses.iter().enumerate() {
        let Ok(closure) = syn::parse_str::<syn::ExprClosure>(raw) else {
            fail(format!("clause {i} is not a closure this tool can parse"), ctx);
            return;
        };
        let Some(syn::Pat::Ident(bind)) = closure.inputs.first().map(strip_type) else {
            fail(format!("clause {i} has no simple result binding"), ctx);
            return;
        };
        let body = rename_word(&tokens(&*closure.body), "self", "probe_self");
        result_binds.push(format!("let {} = &probe_wrong;", bind.ident));
        bodies.push(format!("({body})"));
    }
    if bodies.is_empty() {
        return;
    }

    let call = if is_method {
        format!("probe_self.{}({})", fname, args.join(", "))
    } else {
        format!("{}({})", fname, args.join(", "))
    };
    ctx.seq += 1;
    let name = format!("probe_complete_{}_{}", fname, ctx.seq);
    let rt = tokens(&ret);
    let code = format!(
        "    /// Probes `{fname}` completeness. A SATISFIED cover means a WRONG output\n\
         \x20   /// satisfies the contract, so it does not pin the result (loose contract).\n\
         \x20   #[kani::proof]\n\
         \x20   fn {name}() {{\n\
         \x20       {binds}\n\
         \x20       let probe_correct: {rt} = {call};\n\
         \x20       let probe_wrong: {rt} = kani::any();\n\
         \x20       kani::assume(probe_wrong != probe_correct);\n\
         \x20       {result_binds}\n\
         \x20       kani::cover!({conj}, \"a wrong output satisfies the contract\");\n\
         \x20   }}\n",
        binds = binds.join("\n        "),
        result_binds = result_binds.join("\n        "),
        conj = bodies.join(" && "),
    );
    ctx.rep.probes.push(Probe {
        file: ctx.file.to_path_buf(),
        line: sig.ident.span().start().line,
        func: fname.clone(),
        name,
    code,
    });
}

fn strip_type(p: &syn::Pat) -> syn::Pat {
    match p {
        syn::Pat::Type(t) => (*t.pat).clone(),
        other => other.clone(),
    }
}

fn walk(items: &[Item], self_ty: Option<&syn::Type>, ctx: &mut Ctx) {
    for it in items {
        match it {
            Item::Fn(f) => build(&f.attrs, &f.sig, None, ctx),
            Item::Mod(m) => {
                if let Some((_, inner)) = &m.content {
                    walk(inner, self_ty, ctx);
                }
            }
            Item::Impl(i) => {
                for ii in &i.items {
                    if let ImplItem::Fn(f) = ii {
                        build(&f.attrs, &f.sig, Some(&i.self_ty), ctx);
                    }
                }
            }
            Item::Trait(t) => {
                for ti in &t.items {
                    if let TraitItem::Fn(f) = ti {
                        build(&f.attrs, &f.sig, None, ctx);
                    }
                }
            }
            _ => {}
        }
    }
}

fn rust_files(root: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(p) = stack.pop() {
        if p.is_dir() {
            if p.file_name()
                .and_then(|s| s.to_str())
                .is_some_and(|s| matches!(s, "target" | ".git" | "node_modules"))
            {
                continue;
            }
            if let Ok(rd) = std::fs::read_dir(&p) {
                for e in rd.flatten() {
                    stack.push(e.path());
                }
            }
        } else if p.extension().and_then(|s| s.to_str()) == Some("rs") {
            out.push(p);
        }
    }
    out
}

/// Probe postconditions (`#[ensures]`): does a clause hold for every value its
/// return type admits, proving nothing.
pub fn generate(root: &Path) -> ProbeReport {
    generate_impl(root, false, false)
}

/// Probe preconditions (`#[requires]`): are the assumptions jointly satisfiable,
/// or is every proof under them vacuous. Return-type-independent.
pub fn generate_preconditions(root: &Path) -> ProbeReport {
    generate_impl(root, true, false)
}

/// Probe completeness: does the postcondition accept an output the implementation
/// never produces (loose), or does it uniquely pin the result (tight)?
pub fn generate_completeness(root: &Path) -> ProbeReport {
    generate_impl(root, false, true)
}

fn generate_impl(root: &Path, precond: bool, completeness: bool) -> ProbeReport {
    let mut rep = ProbeReport::default();
    let mut known = HashSet::new();
    let files = rust_files(root);

    for p in &files {
        if let Ok(src) = std::fs::read_to_string(p) {
            if let Ok(f) = syn::parse_file(&src) {
                collect_arbitrary(&f.items, &mut known);
            }
        }
    }
    rep.arbitrary_types = {
        let mut v: Vec<_> = known.iter().cloned().collect();
        v.sort();
        v
    };

    let mut seq = 0;
    for p in &files {
        let Ok(src) = std::fs::read_to_string(p) else { continue };
        let Ok(f) = syn::parse_file(&src) else { continue };
        let mut ctx = Ctx { file: p, known: &known, rep: &mut rep, seq, precond, completeness };
        walk(&f.items, None, &mut ctx);
        seq = ctx.seq;
    }
    rep
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_verifying_probe_means_its_clause_is_vacuous() {
        let rep = ProbeReport {
            probes: vec![
                Probe { file: "t.rs".into(), line: 1, func: "a".into(), name: "probe_vacuity_a_1".into(), code: String::new() },
                Probe { file: "t.rs".into(), line: 2, func: "b".into(), name: "probe_vacuity_b_2".into(), code: String::new() },
            ],
            ..Default::default()
        };
        let out = "Checking harness m::probe_vacuity_b_2...\nVERIFICATION:- FAILED\n\
                   Checking harness m::probe_vacuity_a_1...\nVERIFICATION:- SUCCESSFUL\n";
        let r = interpret(&rep, out);
        assert_eq!(r[0].1, Some(true), "a verifying probe is a vacuous clause");
        assert_eq!(r[1].1, Some(false));
    }

    /// A probe with no verdict in the output DID NOT RUN. Reporting it as healthy would be
    /// this tool's own defect, one level up from the one it looks for.
    #[test]
    fn a_probe_missing_from_the_output_is_unknown_not_passing() {
        let rep = ProbeReport {
            probes: vec![Probe {
                file: "t.rs".into(), line: 1, func: "a".into(),
                name: "probe_vacuity_a_1".into(), code: String::new(),
            }],
            ..Default::default()
        };
        assert_eq!(interpret(&rep, "nothing here").first().unwrap().1, None);
    }

    /// Fixtures need a receiver type `kani::any()` can produce, which is what a real
    /// crate provides via a derive or a hand-written impl. Without it the generator
    /// correctly refuses to probe, which is what the first draft of these tests hit.
    const ARB_THING: &str = "impl kani::Arbitrary for Thing { fn any() -> Self { todo!() } }
";

    fn gen(src: &str) -> ProbeReport {
        let dir = std::env::temp_dir().join(format!("backed_probe_{}", src.len()));
        let _ = std::fs::create_dir_all(&dir);
        std::fs::write(dir.join("t.rs"), format!("{ARB_THING}{src}")).unwrap();
        let r = generate(&dir);
        let _ = std::fs::remove_dir_all(&dir);
        r
    }

    #[test]
    fn a_clause_on_a_probeable_type_produces_a_harness() {
        let r = gen(r#"
            impl Thing {
                #[ensures(|result| result.get() > 0)]
                pub fn count(self) -> NonZero<u32> { todo!() }
            }
        "#);
        assert_eq!(r.clauses_seen, 1);
        assert_eq!(r.probes.len(), 1);
        assert!(r.probes[0].code.contains("kani::any()"));
        assert!(r.probes[0].code.contains("assert!"));
    }

    /// THE RESULT IS ALWAYS BOUND BY REFERENCE. Kani's `ensures` macro binds it as `&T`,
    /// which is why real clauses deref it. Binding by value makes those probes fail to
    /// compile, and this caught it on `Alignment::mask`.
    #[test]
    fn a_dereferencing_clause_still_compiles_because_result_is_a_reference() {
        let r = gen(r#"
            impl Thing {
                #[ensures(|result| *result > 0)]
                pub fn mask(self) -> usize { todo!() }
            }
        "#);
        assert_eq!(r.probes.len(), 1);
        let c = &r.probes[0].code;
        assert!(c.contains("let probe_result: usize = kani::any();"), "{c}");
        assert!(c.contains("let result = &probe_result;"), "{c}");
    }

    /// `self` is a keyword and cannot name a local, so it is renamed. The rename must be
    /// word-exact: an identifier merely containing "self" must survive untouched.
    #[test]
    fn self_is_renamed_word_exactly() {
        let r = gen(r#"
            impl Thing {
                #[ensures(|result| *result == self.align() && myself == 1)]
                pub fn f(self) -> usize { todo!() }
            }
        "#);
        let c = &r.probes[0].code;
        assert!(c.contains("let probe_self: Thing = kani::any();"), "{c}");
        assert!(c.contains("probe_self . align ()"), "{c}");
        assert!(c.contains("myself"), "an identifier containing `self` was mangled: {c}");
    }

    /// `Self` in return position means the impl type. Without resolving it, every
    /// constructor in an impl block gets skipped as an unknown type.
    #[test]
    fn self_return_type_resolves_to_the_impl_type() {
        let r = gen(r#"
            impl Alignment {
                #[ensures(|result| result.as_usize() == align)]
                pub fn new_unchecked(align: usize) -> Self { todo!() }
            }
            impl kani::Arbitrary for Alignment { fn any() -> Self { todo!() } }
        "#);
        assert_eq!(r.probes.len(), 1, "skips: {:?}", r.skips);
        assert!(r.probes[0].code.contains("probe_result: Alignment"), "{}", r.probes[0].code);
    }

    /// EVERY SKIP IS COUNTED AND EXPLAINED. A generator that silently emitted fewer probes
    /// than there are clauses would report a clean bill of health for clauses it never read.
    #[test]
    fn unprobeable_things_are_skipped_with_a_reason_never_silently() {
        let r = gen(r#"
            impl Thing {
                #[ensures(|result| result.is_null())]
                pub fn raw(self) -> *const u8 { todo!() }

                #[ensures(|result| true)]
                pub fn generic<T>(self) -> u8 { todo!() }

                #[ensures(|result| true)]
                pub fn unknown(self) -> SomeForeignType { todo!() }
            }
        "#);
        assert_eq!(r.clauses_seen, 3);
        assert_eq!(r.probes.len(), 0);
        assert_eq!(r.skips.len(), 3, "a skipped clause must still be accounted for");
        let reasons = r.skips.iter().map(|s| s.reason.as_str()).collect::<Vec<_>>().join(" | ");
        assert!(reasons.contains("raw pointer"), "{reasons}");
        assert!(reasons.contains("generic"), "{reasons}");
        assert!(reasons.contains("Arbitrary"), "{reasons}");
    }

    /// A hand-written `impl kani::Arbitrary for T` makes `T` probeable. Without this the
    /// generator would skip every domain type a crate has bothered to make arbitrary.
    #[test]
    fn a_hand_written_arbitrary_impl_makes_a_type_probeable() {
        let r = gen(r#"
            impl kani::Arbitrary for Widget { fn any() -> Self { todo!() } }
            impl Thing {
                #[ensures(|result| result.ok())]
                pub fn make(self) -> Widget { todo!() }
            }
        "#);
        assert!(r.arbitrary_types.contains(&"Widget".to_string()));
        assert_eq!(r.probes.len(), 1, "skips: {:?}", r.skips);
    }

    /// Inputs are havocked too. Vacuity quantifies over inputs as well as results, so a
    /// probe that fixed the inputs would answer a weaker question than the theorem.
    #[test]
    fn inputs_are_havocked_not_fixed() {
        let r = gen(r#"
            impl Thing {
                #[ensures(|result| *result == a)]
                pub fn f(self, a: u32, b: u8) -> u32 { todo!() }
            }
        "#);
        let c = &r.probes[0].code;
        assert!(c.contains("let a: u32 = kani::any();"), "{c}");
        assert!(c.contains("let b: u8 = kani::any();"), "{c}");
    }

    fn gen_pre(src: &str) -> ProbeReport {
        let dir = std::env::temp_dir().join(format!("vac_pre_{}", src.len()));
        let _ = std::fs::create_dir_all(&dir);
        std::fs::write(dir.join("t.rs"), src).unwrap();
        let r = generate_preconditions(&dir);
        let _ = std::fs::remove_dir_all(&dir);
        r
    }

    /// A precondition probe havocs the inputs, assumes every #[requires], and covers.
    /// It never binds or constructs the result: preconditions are return-type-independent.
    #[test]
    fn preconditions_produce_a_cover_probe_ignoring_the_return_type() {
        let r = gen_pre(r#"
            #[kani::requires(x > 10)]
            #[kani::requires(x < 5)]
            fn contradictory(x: u32) -> u32 { x }
        "#);
        assert_eq!(r.probes.len(), 1);
        let c = &r.probes[0].code;
        assert!(c.contains("let x: u32 = kani::any();"), "{c}");
        assert!(c.contains("kani::assume(x > 10)"), "{c}");
        assert!(c.contains("kani::assume(x < 5)"), "{c}");
        assert!(c.contains("kani::cover!(true"), "{c}");
        assert!(!c.contains("probe_result"), "precondition probe must not construct a result: {c}");
    }

    /// For a precondition probe both a satisfiable and an unsatisfiable assume set print
    /// VERIFICATION:- SUCCESSFUL; only the cover status tells them apart. UNREACHABLE means
    /// the preconditions are vacuous.
    #[test]
    fn precondition_vacuity_is_read_from_cover_status_not_the_verdict() {
        let rep = ProbeReport {
            probes: vec![
                Probe { file: "t.rs".into(), line: 1, func: "bad".into(), name: "probe_precond_bad_1".into(), code: String::new() },
                Probe { file: "t.rs".into(), line: 2, func: "ok".into(), name: "probe_precond_ok_2".into(), code: String::new() },
            ],
            ..Default::default()
        };
        let out = "Checking harness probe_precond_bad_1...\n\
                   Status: UNREACHABLE\nVERIFICATION:- SUCCESSFUL\n\
                   Checking harness probe_precond_ok_2...\n\
                   Status: SATISFIED\nVERIFICATION:- SUCCESSFUL\n";
        let r = interpret(&rep, out);
        assert_eq!(r[0].1, Some(true), "UNREACHABLE cover = vacuous preconditions");
        assert_eq!(r[1].1, Some(false), "SATISFIED cover = healthy preconditions");
    }
}

/// Map Kani's output back onto the clauses that produced it.
///
/// CLOSING THE LOOP WITHOUT TOUCHING YOUR SOURCE. Running the probes means pasting them
/// into the crate under test, and this tool will not edit your files to do it. So it reads
/// the output afterwards and says which CLAUSE each verdict belongs to, because
/// `probe_vacuity_as_usize_3` is not something anyone should decode by hand.
///
/// A harness that VERIFIED means its clause is vacuous. A harness absent from the output is
/// reported as unknown, never as passing: a probe that did not run tells you nothing, and
/// treating silence as health is this tool's own subject matter.
pub fn interpret<'a>(rep: &'a ProbeReport, kani_output: &str) -> Vec<(&'a Probe, Option<bool>)> {
    let mut out = Vec::new();
    for p in &rep.probes {
        let mut verdict = None;
        let mut idx = 0;
        let is_precond = p.name.starts_with("probe_precond_");
        let is_complete = p.name.starts_with("probe_complete_");
        while let Some(rel) = kani_output[idx..].find(&p.name) {
            let at = idx + rel;
            let tail = &kani_output[at + p.name.len()..];
            let stop = tail.find("Checking harness").unwrap_or(tail.len());
            let window = &tail[..stop];
            // Match the per-check STATUS line, not the bare word: the summary line
            // "0 of 1 cover properties satisfied" contains "satisfied" and would
            // otherwise misread an unsatisfiable cover. Kani reports a cover as
            // "Status: SATISFIED" (fired) or "Status: UNSATISFIABLE" / "Status:
            // UNREACHABLE" (never fires).
            let cover_fired = window.contains("Status: SATISFIED");
            let cover_dead = window.contains("Status: UNSATISFIABLE") || window.contains("Status: UNREACHABLE");
            if is_precond {
                // cover!(true) after the assumes: UNREACHABLE => preconditions
                // unsatisfiable => vacuous. SATISFIED => reachable => healthy.
                if cover_dead {
                    verdict = Some(true);
                    break;
                }
                if cover_fired {
                    verdict = Some(false);
                    break;
                }
            } else if is_complete {
                // SATISFIED => a wrong output satisfies the contract => LOOSE (the finding).
                // UNSATISFIABLE/UNREACHABLE => only the true output passes => tight.
                if cover_fired {
                    verdict = Some(true);
                    break;
                }
                if cover_dead {
                    verdict = Some(false);
                    break;
                }
            } else {
                if window.contains("VERIFICATION:- SUCCESSFUL") {
                    verdict = Some(true);
                    break;
                }
                if window.contains("VERIFICATION:- FAILED") {
                    verdict = Some(false);
                    break;
                }
            }
            idx = at + p.name.len();
        }
        out.push((p, verdict));
    }
    out
}

/// A module that can be pasted into the crate under test.
///
/// `std_mode` adds `#[unstable(feature = "kani", issue = "none")]`, which the
/// Rust standard library requires on every new item but which does NOT compile
/// in an ordinary crate. Default (false) omits it so the probes build in any
/// crate; pass `--std` when pasting into verify-rust-std.
pub fn render_module(rep: &ProbeReport, std_mode: bool, precond: bool, completeness: bool) -> String {
    let mut s = String::new();
    if completeness {
        s.push_str(
            "// GENERATED COMPLETENESS PROBES. Each havocs the inputs, calls the real function\n\
             // for the correct output, havocs a DIFFERENT output, and covers the postcondition\n\
             // on it. A SATISFIED cover means a WRONG output satisfies the contract, so the\n\
             // contract is LOOSE (an output-changing mutant survives it). An UNREACHABLE cover\n\
             // means only the true output passes: the contract is tight.\n",
        );
    } else if precond {
        s.push_str(
            "// GENERATED PRECONDITION PROBES. Each havocs the inputs, assumes every\n\
             // #[requires] clause, then covers reachability. AN UNREACHABLE COVER MEANS THE\n\
             // PRECONDITIONS ARE JOINTLY UNSATISFIABLE, so no input reaches the body and every\n\
             // proof under them is vacuous. A SATISFIED cover is the healthy outcome.\n",
        );
    } else {
        s.push_str(
            "// GENERATED VACUITY PROBES. Each havocs the inputs and the result and asserts one\n\
             // postcondition. VERIFICATION SUCCESS MEANS THE CLAUSE IS VACUOUS: it holds for every\n\
             // value the return type admits, so every implementation satisfies it and proving it\n\
             // establishes nothing. Failure is the healthy outcome.\n",
        );
    }
    s.push_str("#[cfg(kani)]\n");
    if std_mode {
        s.push_str("#[unstable(feature = \"kani\", issue = \"none\")]\n");
    }
    s.push_str("pub mod vacuity_probes {\n\x20   use super::*;\n\n");
    for p in &rep.probes {
        s.push_str(&p.code);
        s.push('\n');
    }
    s.push_str("}\n");
    s
}
