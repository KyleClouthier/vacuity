/-
  ONE QUERY DECIDES POSTCONDITION COMPLETENESS (MUTATION ADEQUACY).

  `Vacuity.lean` decides whether a postcondition holds for EVERY return value (the empty,
  vacuous end). This file decides the opposite end: whether a postcondition accepts a return
  value the implementation NEVER produces, so that an output-changing implementation still
  satisfies it. That is exactly what mutation-adequacy testing measures one mutant at a
  time, and the same constant-function collapse makes it a single query: havoc a wrong
  output `b` (assume `b ≠ f a`) and cover `P a b`. The cover is SATISFIABLE iff the
  contract is loose.

  PRIOR ART (recorded before any claim is made). Mutation adequacy is DeMillo, Lipton and
  Sayward (1978) and Hamlet (1977). Postcondition/specification completeness as a
  mutation-derived metric, and the output-perturbation check ("does the postcondition
  accept an incorrect output"), are an active area: POSTCONDBENCH (2026) and the
  completeness-lemma / perturbation line of work; Certora's Gambit mutates smart-contract
  specifications for the same end. None of the mathematics below is new. What is done here
  is the contract-shaped, machine-checked statement of why one query suffices, and why it
  dominates a finite mutant campaign, matching `havoc_decides_vacuity` at the other end.
-/

namespace Completeness

variable {A B : Type}

/-- The return type invariant the compiler guarantees (as in `Vacuity.lean`). -/
def TypeValid (I : B → Prop) (g : A → B) : Prop := ∀ a, I (g a)

/-- Some value OTHER than the true output `f a` satisfies the postcondition. Then an
    output-changing implementation survives the proof: the contract is LOOSE. -/
def Loose (f : A → B) (P : A → B → Prop) : Prop :=
  ∃ a b, b ≠ f a ∧ P a b

/-- Only the true output satisfies the postcondition, at every input: the contract is
    TIGHT. This is exactly the negation of `Loose`. -/
def Tight (f : A → B) (P : A → B → Prop) : Prop :=
  ∀ a b, P a b → b = f a

/-!
### The main theorem

Looseness is exactly the survival of an output-changing, type-valid implementation. The
one-query cover (a wrong, admissible output that satisfies `P`) is inhabited precisely when
some `g ≠ f` still satisfies the postcondition where it differs. As in
`havoc_decides_vacuity`, the witness is the CONSTANT function.
-/

theorem loose_iff_output_mutant_survives
    (I : B → Prop) (f : A → B) (P : A → B → Prop) :
    (∃ a b, b ≠ f a ∧ I b ∧ P a b)
      ↔ (∃ (g : A → B) (a : A), TypeValid I g ∧ g a ≠ f a ∧ P a (g a)) := by
  constructor
  · rintro ⟨a, b, hne, hIb, hP⟩
    exact ⟨fun _ => b, a, fun _ => hIb, hne, hP⟩
  · rintro ⟨g, a, hg, hne, hP⟩
    exact ⟨a, g a, hne, hg a, hP⟩

/-!
### Mutation adequacy is sound but incomplete

A surviving output-changing mutant is a genuine proof of looseness: one witness suffices.
But no finite set of KILLED mutants can establish tightness, because an untried wrong
output may still survive.
-/

/-- A surviving output-changing mutant PROVES the contract is loose. -/
theorem adequacy_sound (f : A → B) (P : A → B → Prop)
    (m : A → B) (a : A) (hne : m a ≠ f a) (hP : P a (m a)) :
    Loose f P :=
  ⟨a, m a, hne, hP⟩

/-- A finite set of output-changing mutants that are all KILLED (each violates `P`) is
    consistent with a LOOSE contract, so killing a mutant set cannot establish tightness.
    Witness: true output `0`, a clause accepting `{0, 1}`, one killed mutant returning `2`,
    while `1` survives. -/
theorem adequacy_incomplete :
    ∃ (f : Unit → Nat) (P : Unit → Nat → Prop) (M : List (Unit → Nat)),
      M ≠ [] ∧ (∀ m ∈ M, ¬ P () (m ())) ∧ Loose f P := by
  refine ⟨fun _ => 0, fun _ b => b = 0 ∨ b = 1, [fun _ => 2], by simp, ?_, ?_⟩
  · intro m hm
    simp only [List.mem_singleton] at hm
    subst hm
    decide
  · exact ⟨(), 1, by decide, Or.inr rfl⟩

/-!
### The endpoints
-/

/-- A tight contract is not loose. -/
theorem tight_not_loose (f : A → B) (P : A → B → Prop) (ht : Tight f P) : ¬ Loose f P := by
  rintro ⟨a, b, hne, hP⟩
  exact hne (ht a b hP)

/-- Tight and not-loose are the same property, so the single cover query decides
    completeness in both directions: SATISFIABLE means loose, UNSATISFIABLE means tight. -/
theorem tight_iff_not_loose (f : A → B) (P : A → B → Prop) :
    Tight f P ↔ ¬ Loose f P := by
  constructor
  · exact tight_not_loose f P
  · intro h a b hP
    rcases Classical.em (b = f a) with heq | hne
    · exact heq
    · exact absurd ⟨a, b, hne, hP⟩ h

/-!
### Axiom audit
-/

#print axioms loose_iff_output_mutant_survives
#print axioms adequacy_sound
#print axioms adequacy_incomplete
#print axioms tight_not_loose
#print axioms tight_iff_not_loose

end Completeness
