# vacuity

**Paper:** [Passing Proofs That Prove Nothing](https://doi.org/10.5281/zenodo.21865171) (DOI 10.5281/zenodo.21865171, CC BY 4.0).

Some postconditions prove nothing at all.

```rust
#[ensures(|result| result.get() > 0)]
pub const fn count_ones(self) -> NonZero<u32>
```

The return type is `NonZero<u32>`. Its invariant is already non-zero. So that clause holds
for **every implementation that could ever be written**, including one that ignores its
input and returns `1`. The proof passes. It establishes nothing.

No reachability analysis finds this, because nothing is unreachable. The assertion runs,
the harness is healthy, the verdict is correct. The clause is the problem.

`vacuity` decides it, one query per clause.

## Use

Postconditions (`#[ensures]`), the default:

```console
$ vacuity ./src --out probes.rs
  postconditions found : 13
    covered by a probe   : 10
    skipped (unprobeable): 3
  probes generated     : 10

$ # paste probes.rs into the crate under test
$ cargo kani --harness probe_vacuity_ > out.txt

$ vacuity ./src --results out.txt
  1 clauses are PROVEN VACUOUS.
  Each holds for every value its return type admits, so every
  implementation satisfies it and proving it establishes nothing.

    src/ptr/alignment.rs:95  new_unchecked
```

**Verification success is the bug report.** Failure is the healthy outcome: it produces a
type-valid value your clause rejects, proving the clause constrains something.

Preconditions (`#[requires]`), with `--preconditions`:

```console
$ vacuity ./src --preconditions --out probes.rs
$ cargo kani --harness probe_precond_ > out.txt
$ vacuity ./src --preconditions --results out.txt
  1 functions have VACUOUS PRECONDITIONS.
  Their #[requires] clauses are jointly unsatisfiable, so no input
  reaches the body and every proof under them checks nothing.

    src/alloc.rs:42  allocate
```

Here an **unreachable cover** is the bug report: it means no input satisfies the
assumptions. This half is return-type-independent, so it reaches functions the
postcondition probes skip. See [Both kinds of vacuity](#both-kinds-of-vacuity).

Completeness (`#[ensures]` too tight?), with `--completeness`:

```console
$ vacuity ./src --completeness --out probes.rs
$ cargo kani --harness probe_complete_ > out.txt
$ vacuity ./src --completeness --results out.txt
  1 contracts are LOOSE (incomplete).
  A return value the implementation never produces still satisfies the
  postcondition, so an output-changing implementation survives it.

    src/duration/mod.rs:222  from_seconds
```

This is the dual of vacuity, and the one-query decision form of mutation adequacy: it
calls the real function for the correct output, havocs a *different* output, and covers
the postcondition on it. A **satisfied cover** means a wrong output passes the contract,
so some output-changing implementation would survive it (the contract is loose); an
**unreachable/unsatisfiable cover** means only the true output passes (the contract is
tight). One query decides this over the entire output space, versus running many mutants.
See [Completeness](#completeness).

Every mode exits 1 when it finds a problem, so all three work as a CI gate on new contracts.

Both `#[ensures]` / `#[requires]` and the fully-qualified `#[kani::ensures]` /
`#[kani::requires]` spellings are recognised, including `#[cfg_attr(kani, kani::ensures(...))]`.

### Flags

| flag | effect |
|---|---|
| `--out FILE` | write the generated probe module to `FILE` |
| `--results FILE` | read Kani's output and report the findings |
| `--preconditions` | probe `#[requires]` (unsatisfiable assumptions) instead of `#[ensures]` |
| `--completeness` | probe whether a postcondition is loose (accepts a wrong output) |
| `--std` | add the `#[unstable(feature = "kani")]` attr the standard library requires (omit for an ordinary crate) |

## Install

```console
cargo install vacuity
```

No prebuilt binaries on purpose. It reads your code, so you should be able to read its
source first. Two dependencies, no network, no database, no telemetry.

## Why one query is enough

A probe replaces the function body with an arbitrary value of its return type and asserts
the clause against it. That looks like a sample. It is not.

```lean
theorem havoc_decides_vacuity (I : B → Prop) (P : A → B → Prop) :
    Vacuous I P ↔ ∀ g : A → B, TypeValid I g → Satisfies P g
```

The right-hand side quantifies over **every type-valid implementation anyone could
write**. The left is the single query. They are equivalent, and the hard direction is one
line: for any admissible value `b`, the constant function returning `b` is itself a
type-valid implementation, so it already lies inside the quantifier.

The proof is in [`lean/Vacuity.lean`](lean/Vacuity.lean), machine-checked, no `sorry`, no
external libraries. Three of its seven theorems depend on no axioms at all.

## Compared to writing mutants

Mutation testing answers this by hand: break the function, see whether the proof notices.

|  | mutation | probe |
|---|---|---|
| queries | one build per mutant | one per clause |
| on success | **nothing learned** | vacuous, proved |
| on failure | not vacuous | not vacuous, with a witness |
| needs a working harness | yes | **no** |

That last row is not a technicality. `Alignment::of` in the Rust standard library has its
harness disabled behind [kani#3905](https://github.com/model-checking/kani/issues/3905),
and its clause was still decided, because the probe never calls the function. You can
check a specification before you can check the code.

## What it skips, and why it tells you

A clause is probeable only when every type involved can be produced by `kani::any()`.
Generics, raw pointers, references and unknown user types cannot be, and **every skip is
printed with its reason**:

```
  --- not probed, with reasons ---
    1  generic function, no type arguments to instantiate
       of
    1  return type: `Self` has no kani::Arbitrary this tool can see
       new
```

A generator that quietly emitted fewer probes than there are clauses would report a clean
bill of health for clauses it never read. The counts reconcile at the clause level to make
that impossible to hide: `found` always equals `covered by a probe` plus
`skipped (unprobeable)`, so no clause goes unaccounted. Likewise, a probe missing from the
Kani output is reported as **unknown**, never as passing, and exits 2.

Hand-written `impl kani::Arbitrary for T` blocks are detected, so your domain types count.

## The assumption this rests on

A probe replaces the result with `kani::any::<ReturnType>()`. That substitution is only
legitimate if **`kani::any` can produce every value the function could actually return**.

The two ways that can fail are not symmetric, and the asymmetry is the reason this is
usable at all:

| if `Arbitrary` produces | effect | direction |
|---|---|---|
| more values than the function can return | the clause is tested against unreachable values, fails more often | **under-reports**: misses vacuous clauses, invents nothing |
| fewer values than the function can return | a reachable counterexample is never generated | **over-reports**: calls a clause vacuous when it is not |

Only the second is dangerous, because a false claim about someone's contract costs more
than every true one it might find. So: **a hand-written `impl kani::Arbitrary` that does
not cover its type can make this tool wrong.** Derived instances and the standard ones are
fine. If you wrote a narrow one, this will trust it.

The general condition is proved in [`lean/Collapse.lean`](lean/Collapse.lean): substituting
outcomes for systems is valid for every claim exactly when the generator class is
*pointwise surjective* onto the admissible set, meaning every admissible value is
producible at every input. Constants give that for free, which is why it works for ordinary
per-call postconditions. It stops working when some admissible outcome is unreachable, and
the same file constructs the claim that separates the two checks when it does.

## Limits

- **Vacuous is not the same as weak.** `Alignment::as_usize` probes as having content, and
  its clause is still thin. This decides one precise question.
- **The module is pasted, not injected.** This will not edit your source.
- **Macro-generated functions are invisible**, because `syn` sees a `macro_rules!` body as
  opaque tokens.

## Both kinds of vacuity

Vacuity comes in two flavours and they need different checks. This tool does both.

**Preconditions** (`--preconditions`). An unsatisfiable `assume` means nothing reaches the
assertion, so the property holds over an empty input set. The detector is reachability:
Kani ships `kani::cover` for it. What this adds is the automation around it, one cover probe
per contracted function, havocking the inputs and assuming every `#[requires]` clause, then
reading the cover status back per clause and exiting non-zero for CI. An **UNREACHABLE**
cover is the vacuous case. Note that an unsatisfiable assume set still prints
`VERIFICATION:- SUCCESSFUL`, character for character identical to a real proof, which is
why the signal has to be read from the cover status and why a reviewer scanning verdicts
misses it. A separate [minimal reproduction](https://github.com/KyleClouthier/kani-vacuity-demo)
shows four of five harness styles reporting `SUCCESSFUL` on knowingly broken code for
exactly this reason.

**Postconditions** (the default). The code runs, every input reaches the assertion, the
proof is sound and the verdict is correct. The clause itself has no content.
**Reachability analysis cannot detect this, because nothing is unreachable.** `kani::cover`
sees a completely healthy harness, because the harness *is* healthy. This is the half that
needs the return-value havoc and the [`havoc_decides_vacuity`](lean/Vacuity.lean) theorem
above.

## Completeness

Vacuity asks whether a postcondition holds for *everything* (empty). Completeness asks the
opposite end: does it hold for *too much*, does it accept an output the implementation never
produces? A `#[ensures(|r| *r >= x)]` on a `+ 1` function is not vacuous (a random result can
violate it), but it is loose: `x + 2` satisfies it too, so a `+ 2` bug survives the proof.

`--completeness` decides this in one query per contract: call the real function for the
correct output, havoc a *different* output, and cover the postcondition on it. Satisfiable
means a wrong output passes (loose); unsatisfiable means only the true output passes (tight).
This is the decision form of mutation adequacy over the whole output space rather than a
sampled set of mutants.

Honest limits: it needs the return type to be probeable by `kani::any()` and to be
`PartialEq` (for `wrong != correct`), and it assumes a deterministic return-value contract
(a unique correct output per input). A contract that is *intentionally* a bound will read as
loose, which is correct: the tool reports the fact and the witness, not a judgement of intent.

## Prior art

Nothing here is claimed novel. Vacuity detection is Beer, Ben-David, Eisner and Rodeh (CAV
1997); Kupferman and Vardi established coverage as its dual (CONCUR 2006); Tomb carried it
into deductive verification (2025). Postcondition **completeness** as a mutation-derived
metric, and the output-perturbation check ("does the postcondition accept an incorrect
output"), are an active area: POSTCONDBENCH (2026), completeness-lemma / perturbation work,
and related specification-completeness research.

What is here is those checks mechanised for Rust/Kani contracts, which ship none of them,
where the [std-contracts project goal](https://rust-lang.github.io/rust-project-goals/2025h1/std-contracts.html)
is moving safety conditions from documentation into programmatic contracts and describes no
mechanism for checking whether a ported contract is either empty or too loose.

## Licence

MIT OR Apache-2.0.
