//! `vacuity` -- find postconditions that prove nothing.
//!
//!     vacuity <path> --out probes.rs
//!     # paste probes.rs into the crate, then
//!     cargo kani --harness probe_vacuity_ > out.txt
//!     vacuity <path> --results out.txt
//!
//! A clause is VACUOUS when it holds for every value its return type admits. Every
//! implementation then satisfies it, so proving it establishes nothing, and no
//! reachability analysis detects that because nothing is unreachable.
//!
//! `Vacuity.lean` proves one query decides it. VERIFICATION SUCCESS IS THE BUG REPORT.

use std::path::Path;

const USAGE: &str = "\
vacuity -- find postconditions that prove nothing.

    #[ensures(|result| result.get() > 0)]
    pub const fn count_ones(self) -> NonZero<u32>

The return type is already non-zero, so that clause holds for every implementation
that could ever be written. The proof passes and establishes nothing.

USAGE:
    vacuity <path> --out FILE        generate one probe per postcondition
    vacuity <path> --results FILE    read Kani's output, say which clauses are vacuous
    vacuity <path> --out FILE --std  add the #[unstable] attr the standard library
                                     requires (omit for an ordinary crate)
    vacuity <path> --preconditions   probe #[requires] instead of #[ensures]:
                                     a cover that comes back UNREACHABLE means the
                                     preconditions are unsatisfiable (vacuous)

WORKFLOW:
    vacuity ./src --out probes.rs
    # paste probes.rs into the crate under test
    cargo kani --harness probe_vacuity_ > out.txt
    vacuity ./src --results out.txt

A probe that VERIFIES means its clause is vacuous. Failure is the healthy outcome.

EXIT CODES:
    0  no vacuous clause found
    1  at least one clause is proven vacuous
    2  bad arguments, or a probe produced no verdict at all
";

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() || args.iter().any(|a| a == "-h" || a == "--help") {
        print!("{USAGE}");
        std::process::exit(0);
    }
    let flag = |name: &str| -> Option<String> {
        args.iter().position(|a| a == name).and_then(|i| args.get(i + 1)).cloned()
    };
    let path = args
        .iter()
        .find(|a| !a.starts_with("--"))
        .cloned()
        .unwrap_or_else(|| ".".into());

    let preconditions = args.iter().any(|a| a == "--preconditions");
    let rep = if preconditions {
        vacuity::probe::generate_preconditions(Path::new(&path))
    } else {
        vacuity::probe::generate(Path::new(&path))
    };

    eprintln!("  {} found : {}",
        if preconditions { "precondition clauses" } else { "postconditions" }, rep.clauses_seen);
    eprintln!("  probes generated     : {}", rep.probes.len());
    eprintln!("  skipped              : {}", rep.skips.len());
    if !rep.arbitrary_types.is_empty() {
        eprintln!("  types with a hand-written kani::Arbitrary: {:?}", rep.arbitrary_types);
    }
    // EVERY SKIP IS NAMED. A generator that quietly emitted fewer probes than there are
    // clauses would report a clean bill of health for clauses it never read.
    if !rep.skips.is_empty() {
        eprintln!("\n  --- not probed, with reasons ---");
        let mut by_reason: std::collections::BTreeMap<&str, Vec<&str>> = Default::default();
        for s in &rep.skips {
            by_reason.entry(s.reason.as_str()).or_default().push(s.func.as_str());
        }
        for (why, fns) in by_reason {
            eprintln!("  {:3}  {}", fns.len(), why);
            eprintln!("       {}", fns.join(", ").chars().take(140).collect::<String>());
        }
    }

    if let Some(results) = flag("--results") {
        let out = match std::fs::read_to_string(&results) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("vacuity: cannot read {results}: {e}");
                std::process::exit(2);
            }
        };
        let mapped = vacuity::probe::interpret(&rep, &out);
        let vacuous: Vec<_> = mapped.iter().filter(|(_, v)| *v == Some(true)).collect();
        let missing: Vec<_> = mapped.iter().filter(|(_, v)| v.is_none()).collect();

        if !vacuous.is_empty() {
            if preconditions {
                println!("\n  {} functions have VACUOUS PRECONDITIONS.", vacuous.len());
                println!("  Their #[requires] clauses are jointly unsatisfiable, so no input");
                println!("  reaches the body and every proof under them checks nothing.\n");
            } else {
                println!("\n  {} clauses are PROVEN VACUOUS.", vacuous.len());
                println!("  Each holds for every value its return type admits, so every");
                println!("  implementation satisfies it and proving it establishes nothing.\n");
            }
            for (p, _) in &vacuous {
                println!("    {}:{}  {}", p.file.display(), p.line, p.func);
            }
        } else {
            println!("\n  No clause was proven vacuous.");
        }
        if !missing.is_empty() {
            // A probe with no verdict did not run. Silence is not health.
            println!("\n  {} probes produced NO verdict and were not run:", missing.len());
            for (p, _) in missing.iter().take(10) {
                println!("    {}  ({})", p.name, p.func);
            }
            std::process::exit(2);
        }
        std::process::exit(if vacuous.is_empty() { 0 } else { 1 });
    }

    let std_mode = args.iter().any(|a| a == "--std");
    let module = vacuity::probe::render_module(&rep, std_mode, preconditions);
    match flag("--out") {
        Some(f) => {
            if let Err(e) = std::fs::write(&f, &module) {
                eprintln!("vacuity: cannot write {f}: {e}");
                std::process::exit(2);
            }
            eprintln!("\n  wrote {} probes to {f}", rep.probes.len());
            eprintln!("  Paste it into the crate under test, then:");
            eprintln!("    cargo kani --harness probe_vacuity_ > out.txt");
            eprintln!("    vacuity {path} --results out.txt");
        }
        None => print!("{module}"),
    }
}
