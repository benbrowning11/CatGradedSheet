import CatGradedSheet.Q3.Category

namespace CatGradedSheet.Q3

universe u

/-!
# Problem 3.2(b): No Initial Object
-/

/--
Definition: An object I is initial if for every object B,
there exists a unique morphism from I to B.
-/
def IsInitialObject (I : Type u) : Prop :=
  ∀ (B : Type u), ∃! (_f : Entailment I B), True

/--
Two different entailments from Empty to Bool.

E₁ says: the empty list entails true (but not false)
E₂ says: the empty list entails false (but not true)
-/

def emptyToBool_true : Entailment Empty Bool where
  relation := fun es b => (es = []) ∧ (b = true)
  perm_invariant := by
    intro es es' b h_perm ⟨h_empty, h_true⟩
    constructor
    · -- es' = []
      cases es with
      | nil =>
        simp at h_perm
        exact h_perm
      | cons e _ =>
        -- es = e :: _, but e : Empty is impossible
        exact Empty.elim e
    · exact h_true

def emptyToBool_false : Entailment Empty Bool where
  relation := fun es b => (es = []) ∧ (b = false)
  perm_invariant := by
    intro es es' b h_perm ⟨h_empty, h_false⟩
    constructor
    · cases es with
      | nil =>
        simp at h_perm
        exact h_perm
      | cons e _ => exact Empty.elim e
    · exact h_false

/--
These two entailments are distinct.
-/
theorem emptyToBool_distinct : emptyToBool_true ≠ emptyToBool_false := by
  intro h_eq
  -- If equal, relations would be equal
  have h_rel : emptyToBool_true.relation = emptyToBool_false.relation := by
    rw [h_eq]
  -- Evaluate at ([], true)
  have h_true : emptyToBool_true.relation [] true := by
    constructor <;> rfl
  rw [h_rel] at h_true
  obtain ⟨_, h_absurd⟩ := h_true
  -- But true ≠ false
  cases h_absurd

/--
Therefore, Empty is not an initial object.
-/
theorem empty_not_initial : ¬IsInitialObject Empty := by
  intro h_init
  -- If Empty were initial, there would be a unique morphism to Bool
  have h_unique := h_init Bool
  obtain ⟨f, _, h_uniq⟩ := h_unique
  -- But we have two distinct morphisms
  have h_eq1 : emptyToBool_true = f := h_uniq emptyToBool_true trivial
  have h_eq2 : emptyToBool_false = f := h_uniq emptyToBool_false trivial

  have : emptyToBool_true = emptyToBool_false := by
    rw [h_eq1, h_eq2]
  -- Contradiction
  exact emptyToBool_distinct this

/--
Since Empty is the only reasonable candidate for an initial object
-/
theorem no_initial_object : ¬∃ (I : Type u), IsInitialObject I := by
  sorry

end CatGradedSheet.Q3
