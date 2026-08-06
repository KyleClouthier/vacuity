//! A self-contained demonstration that one query decides whether a postcondition is
//! vacuous, with no mutants written and without calling the function under test.
//!
//! Run it:
//!
//!     cargo kani --harness probe_
//!
//! Expected, and the point of the example:
//!
//!     probe_weak_clause_is_vacuous  ... VERIFICATION:- SUCCESSFUL   <- the BUG report
//!     probe_strong_clause_has_teeth ... VERIFICATION:- FAILED       <- the healthy one
//!
//! Success is the bug. A clause that holds for every value its return type admits is
//! satisfied by every possible implementation, so proving it establishes nothing.
//!
//! THE THEOREM. `Vacuous I P  <->  forall g, TypeValid I g -> Satisfies P g`, machine
//! checked in Lean with no `sorry`. The right side quantifies over every implementation
//! that could ever be written; the left is this single query. The proof of the hard
//! direction is one line: for any admissible `b`, the constant function returning `b` is
//! itself a type-valid implementation, so it already lies in the quantifier's range.
//!
//! WHY THIS BEATS WRITING MUTANTS.
//!   * A passing mutant set establishes nothing; this decides the question.
//!   * One query per clause instead of one build per mutant.
//!   * It never calls the function, so it works on clauses whose own harness cannot run
//!     at all. That case is real: `Alignment::of` in the Rust standard library has its
//!     harness disabled behind a Kani issue, and its clause was still decided this way.

use std::num::NonZero;

/// A real function, standing in for `NonZero::count_ones`.
pub fn popcount(x: NonZero<u8>) -> NonZero<u32> {
    // SAFETY: `x` is non-zero, so at least one bit is set.
    unsafe { NonZero::new_unchecked(x.get().count_ones()) }
}

#[cfg(kani)]
mod probes {
    use super::*;

    /// THE WEAK CLAUSE: `result.get() > 0`.
    ///
    /// This is the clause that shipped on `NonZero::count_ones`. The return type is
    /// `NonZero<u32>`, whose invariant is already non-zero, so the clause holds for every
    /// value the type admits. Verification SUCCEEDS, and that success is the finding.
    #[kani::proof]
    fn probe_weak_clause_is_vacuous() {
        let result: NonZero<u32> = kani::any();
        assert!(result.get() > 0);
    }

    /// THE STRONG CLAUSE: `result.get() == x.get().count_ones()`.
    ///
    /// Verification FAILS, and the counterexample is a type-valid return value the clause
    /// rejects. That failure is proof the clause constrains something.
    #[kani::proof]
    fn probe_strong_clause_has_teeth() {
        let x: NonZero<u8> = kani::any();
        let result: NonZero<u32> = kani::any();
        assert!(result.get() == x.get().count_ones());
    }

    /// The real implementation satisfies the strong clause, so the clause is not merely
    /// unsatisfiable. Without this, `probe_strong_clause_has_teeth` failing would be
    /// consistent with a clause nothing can satisfy, which is a different defect.
    #[kani::proof]
    fn the_strong_clause_is_actually_satisfiable() {
        let x: NonZero<u8> = kani::any();
        assert!(popcount(x).get() == x.get().count_ones());
    }
}
