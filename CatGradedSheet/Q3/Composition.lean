import Q3.RelationPrime

open List

namespace Q3

variable {A B C : Type*}

/-! ## Entailment Composition -/

def compRel (F : Entailment B C) (E : Entailment A B) (as : List A) (c : C) : Prop :=
  ∃ (bs : List B) (ass : List (List A)) (h_len : List.length bs = List.length ass),
    -- (1) The input 'as' is a permutation of the concatenated sub-lists
    as ~ (List.flatten ass) ∧
    -- (2) Pairwise Entailment: E holds for each (as_i, b_i) pair
    (∀ (i : Fin (List.length bs)),
      let i_ass : Fin (List.length ass) := i.cast h_len
      let asi := ass.get i_ass
      let bi  := bs.get i
      E asi bi
    ) ∧
    -- (3) The final entailment F holds for the sequence of intermediate results 'bs'
    F bs c

/--
Proof that `compRel` is permutation-invariant.
-/
lemma compRel_perm_invariant (F : Entailment B C) (E : Entailment A B) :
    ∀ {as as' : List A} {c : C}, as' ~ as → compRel F E as c → compRel F E as' c := by
  intros as as' c h_perm h_rel
  obtain ⟨bs, ass, h_len, h_perm_as, h_entail, h_F⟩ := h_rel
  use bs, ass, h_len
  refine ⟨?_, h_entail, h_F⟩
  exact List.Perm.trans h_perm h_perm_as

/--
The composition operation ⊛ : Ent(B, C) × Ent(A, B) → Ent(A, C).
-/
def entailmentComp (F : Entailment B C) (E : Entailment A B) : Entailment A C :=
  {
    relation := compRel F E,
    perm_invariant := compRel_perm_invariant F E
  }

infixl:80 " ⊛ " => entailmentComp

/-! ## Proof of the Constraint: (S ◦ R)' = S' ⊛ R' -/

/--
Proof that `(S ◦ R)' = S' ⊛ R'`.
-/
lemma comp_of_primes_eq_prime_of_comp (R : A → B → Prop) (S : B → C → Prop) :
    (entailmentFromRel S) ⊛ (entailmentFromRel R) = entailmentFromRel (relationComp R S) := by

  ext as c
  let R' := entailmentFromRel R
  let S' := entailmentFromRel S

  -- Goal: `compRel S' R' as c ↔ rPrimeRel (relationComp R S) as c`
  constructor

  --- (LHS → RHS)
  · rintro ⟨bs, ass, h_len, h_perm, h_E, h_F⟩

    obtain ⟨b, h_bs_eq, h_S⟩ : ∃ b, bs = [b] ∧ S b c :=
      rPrimeRel_iff_singleton.mp h_F

    have h_len_ass : List.length ass = 1 := by
      rw [← h_len]
      simp [h_bs_eq]
    obtain ⟨asi, h_ass_eq⟩ := List.length_eq_one_iff.mp h_len_ass

    -- Since length bs = 1, we only check i = 0.
    have h_E_0 := h_E (Fin.mk 0 (by simp [h_bs_eq]))
    simp [h_bs_eq, h_ass_eq, Fin.cast] at h_E_0

    obtain ⟨a, h_asi_eq, h_R⟩ : ∃ a, asi = [a] ∧ R a b :=
      rPrimeRel_iff_singleton.mp h_E_0

    rw [h_ass_eq, h_asi_eq] at h_perm
    simp [List.flatten] at h_perm -- h_perm is now `as = [a]`
    have h_as_eq : as = [a] := by exact h_perm

    -- RHS
    apply rPrimeRel_iff_singleton.mpr
    use a
    -- Prove `as = [a]` and `(relationComp R S) a c`
    constructor
    · exact h_as_eq
    · unfold relationComp
      use b

  ---  (RHS → LHS)
  · intro h_RHS

    obtain ⟨a, h_as_eq, h_comp⟩ : ∃ a, as = [a] ∧ (relationComp R S) a c :=
      rPrimeRel_iff_singleton.mp h_RHS

    -- ∃ b, R a b ∧ S b c
    unfold relationComp at h_comp
    obtain ⟨b, h_R, h_S⟩ := h_comp

    use [b], [[a]]
    refine ⟨?_, ?_, ?_⟩ -- idrk

    -- length [b] = length [[a]]
    · simp

    -- as ~ List.flatten ass
    · rw [h_as_eq]
      simp [List.flatten]
    -- ∀ i
    · constructor
      · intro i
        simp
        unfold entailmentFromRel
        simp
        exact h_R
      · unfold entailmentFromRel
        simp
        exact h_S

end Q3
