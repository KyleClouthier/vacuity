/-
  Return-havoc decides postcondition vacuity, and dominates mutation testing.

  CONTEXT AND PRIOR ART (recorded before any claim is made).
  Vacuity detection is Beer, Ben-David, Eisner, Rodeh, CAV 1997. Kupferman and Vardi
  ("Sanity Checks in Formal Verification", CONCUR 2006) establish that coverage is the
  dual of vacuity. Tomb, "Static Coverage in Deductive Software Verification" (2025),
  carries that into deductive verification. None of the mathematics below is new, and
  the duality it proves is folklore in that literature.

  WHAT IS ACTUALLY DONE HERE. The folklore is machine-checked, in the specific shape a
  contract checker needs: a postcondition over a RETURN VALUE constrained only by its
  type invariant. Theorem `havoc_decides_vacuity` is the operational content: to learn
  whether a clause is vacuous you do NOT need to write mutants. You replace the body
  with an arbitrary value of the return type and re-run the SAME harness, one query.

  MOTIVATING DATA (measured 2026-08-05 on model-checking/verify-rust-std @ 2138bc6,
  Kani 0.67.0 / CBMC 6.8.0):
    NonZero::count_ones      `result.get() > 0`               vacuous, mutant survives
    Layout::dangling         `result.is_aligned()`            vacuous, mutant survives
    Layout::for_value_raw    `result.align().is_power_of_two()` vacuous, mutant survives
  Each is a clause about the return value alone, satisfied by the return type's own
  invariant. That is exactly `Vacuous` below.
-/

namespace Vacuity

variable {A B : Type}

/-- The postcondition holds for EVERY value the return type admits, so it constrains
    nothing about the input-output relation. -/
def Vacuous (I : B → Prop) (P : A → B → Prop) : Prop :=
  ∀ a b, I b → P a b

/-- An implementation is type-valid when every result it produces satisfies the
    return type's invariant. This is what the compiler already guarantees. -/
def TypeValid (I : B → Prop) (g : A → B) : Prop :=
  ∀ a, I (g a)

/-- An implementation satisfies the postcondition. -/
def Satisfies (P : A → B → Prop) (g : A → B) : Prop :=
  ∀ a, P a (g a)

/-!
### The main theorem

Havocking the return value is sound AND complete for vacuity. The right-hand side
quantifies over ALL type-valid implementations at once, which is what a mutation
campaign is trying and failing to approximate one mutant at a time.
-/

theorem havoc_decides_vacuity (I : B → Prop) (P : A → B → Prop) :
    Vacuous I P ↔ ∀ g : A → B, TypeValid I g → Satisfies P g := by
  constructor
  · intro hv g hg a
    exact hv a (g a) (hg a)
  · intro h a b hb
    -- the witness is the CONSTANT implementation returning b; it is type-valid
    -- precisely because b satisfies the invariant.
    exact h (fun _ => b) (fun _ => hb) a

/-!
### Mutation testing is sound but incomplete

Killing a mutant is a genuine refutation of vacuity: one counterexample suffices.
But passing a finite mutant set establishes nothing.
-/

/-- A killed mutant PROVES the clause is not vacuous. -/
theorem mutation_sound (I : B → Prop) (P : A → B → Prop) (m : A → B)
    (hm : TypeValid I m) (hbad : ¬ Satisfies P m) : ¬ Vacuous I P := by
  intro hv
  exact hbad ((havoc_decides_vacuity I P).mp hv m hm)

/-- A finite mutant set that all passes is consistent with a NON-vacuous clause, so
    surviving mutants can never establish vacuity. Witness: one mutant, one clause. -/
theorem mutation_incomplete :
    ∃ (I : Bool → Prop) (P : Unit → Bool → Prop) (M : List (Unit → Bool)),
      M ≠ [] ∧ (∀ m ∈ M, TypeValid I m ∧ Satisfies P m) ∧ ¬ Vacuous I P := by
  refine ⟨fun _ => True, fun _ b => b = true, [fun _ => true], by simp, ?_, ?_⟩
  · intro m hm
    simp only [List.mem_singleton] at hm
    subst hm
    exact ⟨fun _ => trivial, fun _ => rfl⟩
  · intro hv
    exact Bool.noConfusion (hv () false trivial)

/-- The dominance statement. Anything a mutation campaign can conclude, the single
    havoc query also concludes; and there is a case the havoc query decides that no
    finite mutation campaign does. -/
theorem havoc_dominates_mutation :
    (∀ (I : B → Prop) (P : A → B → Prop) (m : A → B),
        TypeValid I m → ¬ Satisfies P m → ¬ Vacuous I P)
    ∧ (∃ (I : Bool → Prop) (P : Unit → Bool → Prop) (M : List (Unit → Bool)),
        M ≠ [] ∧ (∀ m ∈ M, TypeValid I m ∧ Satisfies P m) ∧ ¬ Vacuous I P) :=
  ⟨fun I P m hm hbad => mutation_sound I P m hm hbad, mutation_incomplete⟩

/-!
### The strength equation

For a finite enumeration `bs` of the return type, put

    tot        = #{ b in bs | I b }
    good a     = #{ b in bs | I b and P a b }
    S(P)       = 1 - (1/|A|) * sum over a of  good a / tot

`S` is 0 exactly when the clause is vacuous, and takes its maximum `1 - 1/tot` when the
clause is functional (pins one return value per input). The two theorems below are the
endpoints, stated in Nat so no division or rational arithmetic is needed.
-/

def tot (I : B → Bool) (bs : List B) : Nat :=
  bs.countP I

def good (I : B → Bool) (P : A → B → Bool) (a : A) (bs : List B) : Nat :=
  bs.countP (fun b => I b && P a b)

theorem good_le_tot (I : B → Bool) (P : A → B → Bool) (a : A) (bs : List B) :
    good I P a bs ≤ tot I bs := by
  induction bs with
  | nil => simp [good, tot]
  | cons b t ih =>
    simp only [good, tot, List.countP_cons] at *
    by_cases hI : I b = true <;> by_cases hQ : P a b = true <;>
      simp [hI, hQ] at * <;> omega

/-- `good a = tot` is exactly vacuity restricted to the enumerated values, so the
    numerator of `S` reaching its denominator IS the vacuity condition. -/
theorem good_eq_tot_iff (I : B → Bool) (P : A → B → Bool) (a : A) (bs : List B) :
    good I P a bs = tot I bs ↔ ∀ b ∈ bs, I b = true → P a b = true := by
  induction bs with
  | nil => simp [good, tot]
  | cons b t ih =>
    have hle : good I P a t ≤ tot I t := good_le_tot I P a t
    have hL : good I P a (b :: t) = good I P a t + (if I b && P a b then 1 else 0) := by
      simp [good, List.countP_cons]
    have hR : tot I (b :: t) = tot I t + (if I b then 1 else 0) := by
      simp [tot, List.countP_cons]
    rw [hL, hR]
    by_cases hI : I b = true
    · by_cases hQ : P a b = true
      · rw [if_pos (by simp [hI, hQ]), if_pos hI]
        constructor
        · intro h b' hb' hI'
          rcases List.mem_cons.mp hb' with rfl | hb't
          · exact hQ
          · exact ih.mp (by omega) b' hb't hI'
        · intro h
          have := ih.mpr fun b' hb' hI' => h b' (List.mem_cons_of_mem _ hb') hI'
          omega
      · rw [if_neg (by simp [Bool.and_eq_true, hQ]), if_pos hI]
        constructor
        · intro h; exfalso; omega
        · intro h
          exact absurd (h b List.mem_cons_self hI) hQ
    · rw [if_neg (by simp [Bool.and_eq_true, hI]), if_neg hI]
      constructor
      · intro h b' hb' hI'
        rcases List.mem_cons.mp hb' with rfl | hb't
        · exact absurd hI' hI
        · exact ih.mp (by omega) b' hb't hI'
      · intro h
        have := ih.mpr fun b' hb' hI' => h b' (List.mem_cons_of_mem _ hb') hI'
        omega

/-- The other endpoint. A FUNCTIONAL clause, one that pins the return value uniquely,
    can never be vacuous as soon as the return type admits two distinct values. This is
    why the repaired `count_ones` clause is immune: `result.get() == popcount(self)`
    determines the result, and `NonZero<u32>` admits more than one value. No mutation
    campaign is needed to establish that, and none could establish it. -/
theorem functional_not_vacuous (I : B → Prop) (P : A → B → Prop) (a₀ : A)
    (b₁ b₂ : B) (h₁ : I b₁) (h₂ : I b₂) (hne : b₁ ≠ b₂)
    (hfun : ∀ a b b', P a b → P a b' → b = b') : ¬ Vacuous I P := by
  intro hv
  exact hne (hfun a₀ b₁ b₂ (hv a₀ b₁ h₁) (hv a₀ b₂ h₂))

/-!
### Axiom audit

Every theorem above must rest on nothing but Lean's own foundations. `sorryAx` appearing
in any of these lists would mean the proof is a placeholder.
-/

#print axioms havoc_decides_vacuity
#print axioms mutation_sound
#print axioms mutation_incomplete
#print axioms havoc_dominates_mutation
#print axioms good_le_tot
#print axioms good_eq_tot_iff
#print axioms functional_not_vacuous

end Vacuity
