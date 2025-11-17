import Q3.CategoryLaws
import Mathlib.CategoryTheory.Category.Basic
open CategoryTheory

namespace Q3

/-! ## Category Instance -/

/--
The Type* objects and Entailment morphisms form a Category.
-/
instance : Category (Type*) where
  Hom A B := Entailment A B
  id A := axiomEntailment A
  comp := fun {A B C} f g => g ⊛ f  -- reversed order
  id_comp := fun {A B} f => by
    exact comp_id_proof f
  comp_id := fun {A B} f => by
    -- comp_id is (id ⊛ f)
    exact id_comp_proof f
  assoc := fun {A B C D} f g h => by
    -- inverted due to my weird def of comp
    exact (assoc_proof f g h).symm

end Q3
