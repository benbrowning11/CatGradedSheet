import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Tactic.Basic
import Std

open CategoryTheory
open List

namespace Q3

variable {C_cat : Type*} [Category C_cat]

/-! ## Basic Definitions -/

/-! ### 1. A* (List type) -/
def AStar (A : Type*) := List A

/-! ### 2. Entailment Structure -/
/--
An entailment from `A` to `B` is a relation `E` between `List A` and `B`
that is invariant under permutation of the list.
-/
structure Entailment (A : Type*) (B : Type*) where
  /-- The underlying relation E ⊆ A* × B -/
  relation : (AStar A) → B → Prop
  /-- The permutation invariance property -/
  perm_invariant :
    ∀ {as as' : List A} {b : B}, as' ~ as → relation as b → relation as' b

@[ext]
lemma Entailment.ext {A B : Type*} (E1 E2 : Entailment A B)
  (h_rel : E1.relation = E2.relation) : E1 = E2 := by
  rcases E1 with ⟨rel1, perm1⟩
  rcases E2 with ⟨rel2, perm2⟩
  simp only [mk.injEq]
  exact h_rel

/-- Ent(A, B) is the set (Type) of all entailments from A to B. -/
def Ent (A : Type*) (B :Type*) := Entailment A B

-- We can also add an instance to allow calling an entailment `E`
-- as a function `E as b` instead of `E.relation as b`.
instance {A : Type*} {B : Type*} :
    CoeFun (Entailment A B) (fun _ => List A → B → Prop) :=
  ⟨fun E => E.relation⟩

/-! ### 3. Basic Relations -/

/--
The identity relation `ΔC = { (c, c) | c ∈ C }`.
In Lean, `C → C → Prop` is the type for a relation `R ⊆ C × C`.
The relation `c₁ = c₂` is exactly the identity relation.
-/
def identityRel (C : Type*) (c₁ c₂ : C) : Prop :=
  c₁ = c₂

/--
The composition of relations `R ⊆ A × B` and `S ⊆ B × C`,
defined as `a (S ◦ R) c ⇐⇒ ∃ b ∈ B. a R b ∧ b S c`.
-/
def relationComp {A B C : Type*} (R : A → B → Prop) (S : B → C → Prop) (a : A) (c : C) : Prop :=
  ∃ b : B, R a b ∧ S b c

end Q3
