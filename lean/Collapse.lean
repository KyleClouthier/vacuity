/-
  WHEN DOES CHECKING OUTCOMES REPLACE CHECKING SYSTEMS?

  `Vacuity.lean` proves that deciding whether a postcondition is vacuous needs one query
  over an arbitrary return value, and does not need to quantify over implementations. The
  proof of the hard direction is the CONSTANT function: given an admissible value `b`, the
  process that always returns `b` is itself an admissible process, so quantifying over
  processes already ranges over every outcome.

  That collapse is the whole reason the check is cheap. The space of processes is
  enormous; the space of outcomes is small. And the same shape appears far outside code:

    * an evaluation criterion every admissible answer satisfies
    * a policy constraint every admissible policy satisfies
    * a diagnostic threshold every admissible patient meets
    * a scientific claim no admissible observation could contradict

  In each case the cheap move is to stop enumerating systems and enumerate outcomes. THIS
  FILE ASKS WHEN THAT MOVE IS LEGITIMATE, because it is not always.

  RESULT. The collapse holds for EVERY claim exactly when the generator class is
  POINTWISE SURJECTIVE onto the admissible set: every admissible outcome is producible at
  every input. Constant-closure is one way to get that, and it is sufficient, not
  necessary. When pointwise surjectivity fails, there is a claim that every generator
  satisfies and that is nonetheless false of some admissible outcome, so testing outcomes
  and testing systems come apart.

  PRIOR ART. Recon was run before making any claim, and this has a precise home: it is an
  instance of MARIE-CLAUDE GAUDEL'S TESTABILITY-HYPOTHESIS FRAMEWORK ("Testing can be
  formal, too", TAPSOFT 1995; "Testing from Formal Specifications, a Generic Approach",
  2001). Gaudel derives an EXHAUSTIVE TEST SET from a specification's semantics and shows
  that, under minimal hypotheses on the program under test, success of that set is
  equivalent to satisfaction of the specification. The condition below is one such
  hypothesis, named explicitly and proved NECESSARY as well as sufficient, for one
  specific substitution: outcomes in place of systems.

  The other ingredients are older still. Popper's content measure is `1 - p(P)`, which is
  the specification-strength quantity in `Vacuity.lean` under an earlier name. Vacuity
  detection is Beer, Ben-David, Eisner and Rodeh (CAV 1997), and the coverage dual is
  Kupferman and Vardi (CONCUR 2006).

  NOTHING HERE IS CLAIMED AS NEW. It is recorded because it is CHECKED, and because it
  names a boundary a tool built on the collapse has to respect. Finding out which
  hypothesis your shortcut depends on is worth more than the shortcut.
-/

namespace Collapse

variable {A Ω : Type}

/-- The admissible outcomes. -/
abbrev Admissible (Ω : Type) := Ω → Prop

/-- A generator turns an input into an outcome. Think: an implementation, a policy, a
    model, a measurement procedure. -/
abbrev Gen (A Ω : Type) := A → Ω

/-- `g` only ever produces admissible outcomes. -/
def Sound (I : Admissible Ω) (g : Gen A Ω) : Prop := ∀ a, I (g a)

/-- Every outcome `g` produces satisfies the claim. -/
def Holds (P : A → Ω → Prop) (g : Gen A Ω) : Prop := ∀ a, P a (g a)

/-- CHECKING SYSTEMS: every generator in the class satisfies the claim. -/
def SystemCheck (𝒢 : Gen A Ω → Prop) (P : A → Ω → Prop) : Prop :=
  ∀ g, 𝒢 g → Holds P g

/-- CHECKING OUTCOMES: every admissible outcome satisfies the claim, at every input. -/
def OutcomeCheck (I : Admissible Ω) (P : A → Ω → Prop) : Prop :=
  ∀ a ω, I ω → P a ω

/-- Every admissible outcome is producible at every input. -/
def PointwiseSurjective (𝒢 : Gen A Ω → Prop) (I : Admissible Ω) : Prop :=
  ∀ a ω, I ω → ∃ g, 𝒢 g ∧ g a = ω

/-- Every generator in the class is sound. Without this, checking outcomes says nothing
    about generators that leave the admissible set. -/
def ClassSound (𝒢 : Gen A Ω → Prop) (I : Admissible Ω) : Prop :=
  ∀ g, 𝒢 g → Sound I g

/-!
### The easy direction

Checking outcomes is always at least as strong, provided the class stays inside `I`.
-/

theorem outcome_implies_system
    (𝒢 : Gen A Ω → Prop) (I : Admissible Ω) (P : A → Ω → Prop)
    (hs : ClassSound 𝒢 I) (h : OutcomeCheck I P) :
    SystemCheck 𝒢 P := by
  intro g hg a
  exact h a (g a) (hs g hg a)

/-!
### The dichotomy

The converse holds for EVERY claim exactly when every admissible outcome is producible at
every input.
-/

/-- If every admissible outcome is producible at each input, checking systems is as strong
    as checking outcomes. This is the general form of `havoc_decides_vacuity`: there, the
    class was all sound functions and the witness was the constant. -/
theorem system_implies_outcome_of_surjective
    (𝒢 : Gen A Ω → Prop) (I : Admissible Ω) (P : A → Ω → Prop)
    (hsurj : PointwiseSurjective 𝒢 I) (h : SystemCheck 𝒢 P) :
    OutcomeCheck I P := by
  intro a ω hω
  obtain ⟨g, hg, rfl⟩ := hsurj a ω hω
  exact h g hg a

/-- THE BOUNDARY. If some admissible outcome is NOT producible at some input, then the
    two checks come apart: there is a claim every generator satisfies which is false of an
    admissible outcome.

    The separating claim is diagonal, and it is the natural one: "never produce `ω₀` at
    `a₀`". Every generator satisfies it precisely because none of them can produce `ω₀`
    there, and it is false at `(a₀, ω₀)` by construction. -/
theorem not_surjective_separates
    (𝒢 : Gen A Ω → Prop) (I : Admissible Ω) (a₀ : A) (ω₀ : Ω)
    (hadm : I ω₀) (hmiss : ∀ g, 𝒢 g → g a₀ ≠ ω₀) :
    ∃ P : A → Ω → Prop, SystemCheck 𝒢 P ∧ ¬ OutcomeCheck I P := by
  refine ⟨fun a ω => ¬(a = a₀ ∧ ω = ω₀), ?_, ?_⟩
  · intro g hg a ⟨ha, hω⟩
    exact hmiss g hg (ha ▸ hω)
  · intro h
    exact h a₀ ω₀ hadm ⟨rfl, rfl⟩

/-- Constant-closure is a SUFFICIENT condition, and it is the one the code case uses: the
    class of all sound functions contains every constant. It is not necessary, since a
    class with no constants at all can still reach every outcome at every point. -/
theorem constants_give_surjectivity
    (I : Admissible Ω) (𝒢 : Gen A Ω → Prop)
    (hconst : ∀ ω, I ω → 𝒢 (fun _ => ω)) :
    PointwiseSurjective 𝒢 I := by
  intro a ω hω
  exact ⟨fun _ => ω, hconst ω hω, rfl⟩

/-- Putting it together: under pointwise surjectivity and class soundness, the two checks
    are EQUIVALENT for every claim. This is the licence to test outcomes instead of
    systems. -/
theorem collapse
    (𝒢 : Gen A Ω → Prop) (I : Admissible Ω) (P : A → Ω → Prop)
    (hs : ClassSound 𝒢 I) (hsurj : PointwiseSurjective 𝒢 I) :
    SystemCheck 𝒢 P ↔ OutcomeCheck I P :=
  ⟨system_implies_outcome_of_surjective 𝒢 I P hsurj,
   outcome_implies_system 𝒢 I P hs⟩

/-!
### A concrete class where the collapse FAILS

Pinning one input's output is enough. This is not exotic: it is a protocol whose first
message is fixed, an initialisation contract, a policy with a mandated default, or a model
constrained to refuse on a designated input. In all of those, testing outcomes is strictly
weaker than testing the system, and a tool built on the collapse would be unsound.
-/

/-- Generators forced to answer `c` at `a₀`. -/
def Pinned (a₀ : A) (c : Ω) : Gen A Ω → Prop := fun g => g a₀ = c

theorem pinned_breaks_the_collapse
    [DecidableEq Ω] (a₀ : A) (c ω₀ : Ω) (I : Admissible Ω)
    (hadm : I ω₀) (hne : ω₀ ≠ c) :
    ∃ P : A → Ω → Prop, SystemCheck (Pinned a₀ c) P ∧ ¬ OutcomeCheck I P := by
  refine not_surjective_separates (Pinned a₀ c) I a₀ ω₀ hadm ?_
  intro g hg h
  exact hne (h ▸ hg)

/-!
### Axiom audit
-/

#print axioms outcome_implies_system
#print axioms system_implies_outcome_of_surjective
#print axioms not_surjective_separates
#print axioms constants_give_surjectivity
#print axioms collapse
#print axioms pinned_breaks_the_collapse

end Collapse
