/-
  UNSATISFIABLE PRECONDITIONS MAKE EVERY PROOF VACUOUS, AND ONE REACHABILITY QUERY
  DECIDES IT.

  A `#[requires]` clause becomes an `assume` in the harness. If the conjoined preconditions
  are jointly unsatisfiable, no input reaches the body: every postcondition then holds
  vacuously and the proof under them checks nothing, while Kani still prints
  `VERIFICATION:- SUCCESSFUL`, character for character identical to a real proof. The
  detector is reachability. Havoc the input, assume every clause, and cover a point after
  the assumes; an UNREACHABLE cover means the preconditions are unsatisfiable.

  PRIOR ART (recorded before any claim is made). This is ordinary assume-false / dead-code
  vacuity, the precondition half of Beer, Ben-David, Eisner and Rodeh (CAV 1997); Kani
  ships `kani::cover` for reachability. Nothing below is new. It is the contract-shaped,
  machine-checked statement of why an unsatisfiable assume set voids every proof guarded
  by it, and why one reachability query is enough to detect it.
-/

namespace Precondition

variable {A B : Type}

/-- The conjoined `#[requires]` clauses as a predicate on inputs. -/
def Satisfiable (R : A → Prop) : Prop := ∃ a, R a

/-- No input satisfies the preconditions: the assume set is unsatisfiable, so the harness
    body is unreachable. -/
def VacuousPre (R : A → Prop) : Prop := ∀ a, ¬ R a

/-- Vacuous preconditions are exactly unsatisfiable ones. The reachability cover that Kani
    runs after the assumes is inhabited iff `Satisfiable R`, so an UNREACHABLE cover is
    precisely this vacuity verdict. -/
theorem vacuous_iff_unsat (R : A → Prop) : VacuousPre R ↔ ¬ Satisfiable R := by
  constructor
  · rintro h ⟨a, ha⟩
    exact h a ha
  · intro h a ha
    exact h ⟨a, ha⟩

/-!
### The operational content

Unsatisfiable preconditions make EVERY guarded postcondition hold for EVERY implementation.
That is what "the proof establishes nothing" means precisely: the verdict is independent of
both the specification and the code. `[Inhabited B]` only supplies a return value to name an
implementation; it introduces no axioms.
-/

theorem unsat_iff_everything_vacuous (R : A → Prop) [Inhabited B] :
    VacuousPre R ↔ ∀ (P : A → B → Prop) (g : A → B), ∀ a, R a → P a (g a) := by
  constructor
  · intro h P g a ha
    exact absurd ha (h a)
  · intro h a ha
    -- instantiate the guarded claim with the always-false postcondition; if any input
    -- satisfied R it would force False.
    exact h (fun _ _ => False) (fun _ => default) a ha

/-!
### Axiom audit
-/

#print axioms vacuous_iff_unsat
#print axioms unsat_iff_everything_vacuous

end Precondition
