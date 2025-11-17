import Q3.Defs

open List

namespace Q3


variable {A B C : Type*}

/-! ## The R' Construction -/

/--
This is the relation `R'` itself.
It holds if and only if the list `as` is a singleton `[a]` and `R a b` holds.
-/
def rPrimeRel (R : A → B → Prop) (as : List A) (b : B) : Prop :=
  match as with
  | [a] => R a b  -- The case n=1: as = [a]
  | _   => False  -- All other cases (n=0 or n≥2)

/--
A proof that `rPrimeRel` is permutation-invariant.
-/
lemma rPrimeRel_perm_invariant (R : A → B → Prop) :
    ∀ {as as' : List A} {b : B}, as' ~ as → rPrimeRel R as b → rPrimeRel R as' b := by
  intros as as' b h_perm h_rel
  cases as with
  | nil => simp [rPrimeRel] at h_rel
  | cons a tail =>
    cases tail with
    | nil =>
      have h_eq : as' = [a] := List.Perm.eq_singleton h_perm
      rw [h_eq]
      simp [rPrimeRel]
      apply h_rel
    | cons a' tail' =>
      simp [rPrimeRel] at h_rel

/--
The constructor for the entailment `R'` given a relation `R`.
This function takes `R ⊆ A × B` and returns the entailment `R' ∈ Ent(A, B)`.
-/
def entailmentFromRel (R : A → B → Prop) : Entailment A B :=
  {
    relation := rPrimeRel R,
    perm_invariant := rPrimeRel_perm_invariant R
  }

/--
A helper lemma showing that `rPrimeRel R as b` holds if and only if
`as` is a singleton `[a]` and `R a b` holds.
-/
lemma rPrimeRel_iff_singleton {R : A → B → Prop} {as : List A} {b : B} :
    rPrimeRel R as b ↔ ∃ a, as = [a] ∧ R a b := by
  constructor
  · -- (→) If `rPrimeRel R as b` holds, prove `∃ a, as = [a] ∧ R a b`
    intro h_rel
    cases as with
    | nil =>
      simp [rPrimeRel] at h_rel
    | cons a tail =>
      cases tail with
      | nil =>
        simp [rPrimeRel] at h_rel
        use a
      | cons a' tail' =>
        simp [rPrimeRel] at h_rel
  · -- (←) If `∃ a, as = [a] ∧ R a b` holds, prove `rPrimeRel R as b`
    rintro ⟨a, h_as, h_R⟩
    rw [h_as]
    simp [rPrimeRel, h_R]

@[simp]
lemma rPrimeRel_singleton_iff {R : A → B → Prop} {a : A} {b : B} :
  rPrimeRel R [a] b ↔ R a b := by
  simp [rPrimeRel]

@[simp]
lemma identityRel_refl {C : Type*} {c : C} : identityRel C c c := by
  simp [identityRel]

/--
The axiom entailment `AxC = (ΔC)'`.
We define this by applying our `entailmentFromRel` function
to the `identityRel`.
-/
def axiomEntailment (C : Type*) : Entailment C C :=
  entailmentFromRel (identityRel C)

end Q3
