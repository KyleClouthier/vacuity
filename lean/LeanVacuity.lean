/-
  DOES THE VACUITY PHENOMENON REACH THE KERNEL?

  The paper's thesis is that a passing proof can establish nothing. Kani is a bounded
  model checker. The sharper test is whether the SAME failure survives a full kernel
  proof in Lean, the strongest verifier there is. If it does, "proofs that prove
  nothing" is not a Kani quirk.

  Below is a lemma that LOOKS like a real fact, is accepted by the Lean kernel with no
  `sorry`, and yet establishes nothing, because no value satisfies its hypotheses. This
  is precondition vacuity (Precondition.lean) instantiated on a kernel proof.
-/

namespace LeanVacuity

/-- Looks like a bound-transfer lemma. Kernel-checks. Proves nothing: no `n` is both
    greater than 5 and less than 3, so the conclusion is asserted over an empty domain. -/
theorem plausible_but_vacuous (n : Nat) (h1 : n > 5) (h2 : n < 3) : n = 42 := by
  omega

/-- The detector, and the exact analog of the tool's precondition check: are the
    hypotheses jointly satisfiable? Here they are NOT, and that is provable. An honest
    reviewer wants THIS verdict, which the green checkmark on the lemma above hides. -/
theorem hypotheses_are_unsatisfiable : ¬ ∃ n : Nat, n > 5 ∧ n < 3 := by
  rintro ⟨n, h1, h2⟩
  omega

/-- Contrast: a genuine lemma whose hypotheses ARE satisfiable (n = 7 witnesses them),
    so the conclusion says something about a real object. -/
theorem genuine (n : Nat) (h1 : n > 5) (h2 : n < 10) : n ≥ 6 := by
  omega

theorem genuine_hypotheses_are_satisfiable : ∃ n : Nat, n > 5 ∧ n < 10 :=
  ⟨7, by omega, by omega⟩

/-!
### The point

`#print axioms` reports the vacuous lemma as resting only on the standard foundations,
exactly like the genuine one. Kernel-cleanliness does NOT imply the lemma has content.
The only thing that separates them is the satisfiability of the hypotheses, which is a
SEPARATE query, the same one the vacuity tool runs against Kani contracts.
-/

#print axioms plausible_but_vacuous
#print axioms hypotheses_are_unsatisfiable
#print axioms genuine

end LeanVacuity
