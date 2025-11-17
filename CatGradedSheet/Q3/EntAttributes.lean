import CatGradedSheet.Q3.Category
import CatGradedSheet.Q3.NoInitialObject
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Category.Basic
open CategoryTheory

namespace CatGradedSheet.Q3

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
/-! ## (d) Ent has binary coproducts. -/


/-! ## (e) Ent has exponentials. -/
def HasExponentials : Prop :=
  ∀ (A B : Type*), ∃ (E : Type*) (eval : Entailment (E × A) B),
    ∀ (Z : Type*) (f : Entailment (Z × A) B),
      ∃! (g : Entailment Z E), sorry


end CatGradedSheet.Q3
