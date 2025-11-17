import Q3.Category
import Q3.NoInitialObject
import Q3.NoProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Category.Basic
open CategoryTheory

namespace Q3

/-! # Part 2 -/

/-! ## (a) Ent has a terminal object. -/
def IsTerminal (T : Type*) : Prop :=
  ∀ (A : Type*), ∃! (_f : Entailment A T), True

def toEmpty (A : Type*) : Entailment A Empty where
  relation := fun _ e => Empty.elim e
  perm_invariant := by
    intros as as' e
    exact Empty.elim e

lemma empty_function_unique {α : Type*} (f g : Empty → α) : f = g := by
  ext e
  exact Empty.elim e

lemma empty_relation_unique {A : Type*} (r₁ r₂ : List A → Empty → Prop) : r₁ = r₂ := by
  ext as e
  exact Empty.elim e

theorem entailment_to_empty_unique (A : Type*) (E : Entailment A Empty) :
    E = toEmpty A := by
  ext as e
  exact Empty.elim e

theorem empty_is_terminal : IsTerminal Empty := by
  intro A
  use toEmpty A
  constructor
  · trivial
  · intro f _
    exact entailment_to_empty_unique A f

/-! ## (b) Ent has an initial object.-/

example : ¬∃ (I : Type*), IsInitialObject I := no_initial_object

/-! ## (c) Ent has binary products. -/
example : ¬ IsProduct (proj1 Bool Unit) (proj2 Bool Unit) :=
  Q3.not_IsProduct_proj1_proj2_bool_unit
/-! ## (d) Ent has binary coproducts. -/

def IsCoproduct {S A B : Type} (i1 : Entailment A S) (i2 : Entailment B S) : Prop :=
  ∀ (Z : Type) (f : Entailment A Z) (g : Entailment B Z),
    ∃! (h : Entailment S Z), h ⊛ i1 = f ∧ h ⊛ i2 = g

def inl (A B : Type*) : Entailment A (A ⊕ B) := {
  relation := fun as s => ∃ (a : A), as = [a] ∧ s = Sum.inl a,
  perm_invariant := by
    intros as as' s h_perm h_rel
    obtain ⟨a, h_as, h_s⟩ := h_rel
    rw [h_as] at h_perm
    use a
    constructor
    · exact List.Perm.eq_singleton h_perm
    · exact h_s
}

def inr (A B : Type*) : Entailment B (A ⊕ B) := {
  relation := fun bs s => ∃ (b : B), bs = [b] ∧ s = Sum.inr b,
  perm_invariant := by
    intros bs bs' s h_perm h_rel
    obtain ⟨b, h_bs, h_s⟩ := h_rel
    rw [h_bs] at h_perm
    use b
    constructor
    · exact List.Perm.eq_singleton h_perm
    · exact h_s
}

/-! ## (e) Ent has exponentials. -/
def HasExponentials : Prop :=
  ∀ (A B : Type*), ∃ (E : Type*) (eval : Entailment (E × A) B),
    ∀ (Z : Type*) (f : Entailment (Z × A) B),
      ∃! (g : Entailment Z E), sorry


end Q3
