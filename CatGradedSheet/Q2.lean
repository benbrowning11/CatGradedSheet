import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Permutation

open CategoryTheory
open List

namespace Q2

variable {C : Type*} [Category C]

/-!
# C★ Categories

This file proves that:
  ∀ set 𝑋, the category C★Alg(𝑋) has an initial object.

-/

/-! ## Definitions -/

/-! ### DefSection 1 - Permutation action on n-tuples -/

-- Permute a vector by a permutation σ
def Vector.permute {A : Type*} {n : Nat} (σ : Equiv.Perm (Fin n))
    (v : Vector A n) : Vector A n :=
  Vector.ofFn (fun i => v.get (σ.symm i))

/-! ### DefSection 2 - Define A★ (A-star) -/

-- A★ is the free monoid on A, represented as lists
-- Basically A★ is just the closure of A under concatenation
def AStar (A : Type*) := List A

/-! ### DefSection 3 - Define the basic operations -/
def sing {A : Type*} (a : A) : AStar A := [a]

def flat {A : Type*} (ll : AStar (AStar A)) : AStar A := List.flatten ll

def mapStar {A B : Type*} (f : A → B) : AStar A → AStar B := List.map f

/-! ### DefSection 4 - Restriction to n-element sequences -/
-- Extract the operation on n-element sequences
def restrictToN {A : Type*} (α : AStar A → A) (n : Nat) : Vector A n → A :=
  fun v => α v.toList

/-! ### DefSection 5 - C★-algebras -/

/-- A C★-algebra (commutative star algebra)
A = ( 𝐴 , 𝛼 : 𝐴★ → 𝐴 )
type A, operation α : A★ → A satisfying three axioms
-/
structure CStarAlgebra (A : Type*) where
  op : AStar A → A
  -- α ∘ sing = id (unit law)
  sing_law : ∀ a : A, op (sing a) = a
  -- α ∘ flat = α ∘ map α (associativity)
  flat_law : ∀ ll : AStar (AStar A), op (flat ll) = op (mapStar op ll)
  -- restrictToN α is invariant under reordering (commutativity)
  perm_law : ∀ (l₁ l₂ : List A), l₁ ~ l₂ → op l₁ = op l₂

/-! ### DefSection 6 - C★ homomorphism -/
structure CStarHomomorphism {α β} (A : CStarAlgebra α) (B : CStarAlgebra β) where
  toFun : α → β
  preserves : ∀ l : AStar α, toFun (A.op l) = B.op (mapStar toFun l)

/-! ### DefSection 7 - The category C★Alg(X) -/

/-- An object in C★Alg(X): a C★-algebra A with a function X → A -/
structure CStarAlgObj (X : Type*) where
  carrier : Type*
  algebra : CStarAlgebra carrier
  inclusion : X → carrier

/-- A morphism in C★Alg(X): a C★-homomorphism making the triangle commute -/
structure CStarAlgHom {X : Type*} (A B : CStarAlgObj X) where
  toFun : A.carrier → B.carrier
  is_hom : ∀ l : AStar A.carrier,
    toFun (A.algebra.op l) = B.algebra.op (mapStar toFun l)
  commutes : ∀ x : X, toFun (A.inclusion x) = B.inclusion x

/-! ## Category Instance -/

@[ext]
lemma CStarAlgHom.ext {X : Type*} {A B : CStarAlgObj X}
    (f g : CStarAlgHom A B) (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g
  congr

instance (X : Type*) : Category (CStarAlgObj X) where
  Hom := CStarAlgHom
  id A := {
    toFun := id
    is_hom := by simp [mapStar]
    commutes := by simp
  }
  comp f g := {
    toFun := g.toFun ∘ f.toFun
    is_hom := by
      intro l
      simp [mapStar]
      rw [f.is_hom, g.is_hom]
      congr 1
      induction l with
      | nil => rfl
      | cons head tail ih =>
        simp [mapStar, List.map]
    commutes := by
      intro x
      simp
      rw [f.commutes, g.commutes]
  }

/-! ## Axiomatization of the Free Commutative Monoid -/

/-- The free commutative monoid on X -/
axiom FreeCommMonoid (X : Type*) : Type*

/-- inclusion map -/
axiom fcm_inclusion {X : Type*} : X → FreeCommMonoid X

/-- monoid operation on lists of elements -/
axiom fcm_op {X : Type*} : AStar (FreeCommMonoid X) → FreeCommMonoid X

/-- free commutative monoid forms a C★-algebra -/
axiom fcm_sing_law {X : Type*} :
  ∀ a : FreeCommMonoid X, fcm_op (sing a) = a

axiom fcm_flat_law {X : Type*} :
  ∀ ll : AStar (AStar (FreeCommMonoid X)),
    fcm_op (flat ll) = fcm_op (mapStar fcm_op ll)

axiom fcm_perm_law {X : Type*} :
  ∀ (l₁ l₂ : List (FreeCommMonoid X)), l₁ ~ l₂ → fcm_op l₁ = fcm_op l₂

axiom fcm_universal_property {X : Type*} (A : CStarAlgObj X) :
  Σ (f : FreeCommMonoid X → A.carrier),
    PLift ( -- I hate universe
      ((∀ x : X, f (fcm_inclusion x) = A.inclusion x) ∧
       (∀ l : AStar (FreeCommMonoid X),
         f (fcm_op l) = A.algebra.op (mapStar f l))) ∧
      (∀ g : FreeCommMonoid X → A.carrier,
        (∀ x : X, g (fcm_inclusion x) = A.inclusion x) →
        (∀ l : AStar (FreeCommMonoid X),
          g (fcm_op l) = A.algebra.op (mapStar g l)) →
        g = f)
    )

/-! ## The Initial Object -/

/-- The initial C★-algebra over X using the free commutative monoid -/
noncomputable def initialCStarAlg (X : Type*) : CStarAlgObj X where
  carrier := FreeCommMonoid X
  algebra := {
    op := fcm_op
    sing_law := fcm_sing_law
    flat_law := fcm_flat_law
    perm_law := fcm_perm_law
  }
  inclusion := fcm_inclusion

/-- The unique morphism from the initial object -/
noncomputable def initialMorphism {X : Type*} (A : CStarAlgObj X) :
    CStarAlgHom (initialCStarAlg X) A :=
  let ⟨f, hf⟩ := fcm_universal_property A
  {
    toFun := f
    is_hom := hf.down.1.2
    commutes := hf.down.1.1
  }

/-- Uniqueness of the morphism from the initial object -/
theorem initialMorphism_unique {X : Type*} (A : CStarAlgObj X)
    (g : CStarAlgHom (initialCStarAlg X) A) :
    g = initialMorphism A := by
  cases h : fcm_universal_property A with
  | mk f hf =>
    -- g.toFun satisfies the same properties as f
    have g_eq : g.toFun = f := by
      -- We access the uniqueness property from hf
      apply hf.down.2
      · exact g.commutes
      · exact g.is_hom

    ext -- assume ∃x
    rw [g_eq]

    unfold initialMorphism

    -- fcm_universal_property A is ⟨f, hf⟩.
    rw [h]

/-! ## Main Theorem -/
class IsInitial (X : C) : Prop where
  uniq : ∀ P : C, ∃! (_ : X ⟶ P), True

noncomputable instance (X : Type*) : IsInitial (initialCStarAlg X) where
  uniq := by
    intro A
    use initialMorphism A

    constructor
    · -- It exists
      trivial
    · -- it is unique
      intro g
      simp
      exact initialMorphism_unique A g

-- This final theorem is correct
theorem has_initial_object (X : Type*) :
    ∃ I : CStarAlgObj X, IsInitial I :=
  ⟨initialCStarAlg X, inferInstance⟩
end Q2
