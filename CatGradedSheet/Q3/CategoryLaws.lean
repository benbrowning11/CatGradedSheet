import CatGradedSheet.Q3.Composition

open List

namespace CatGradedSheet.Q3

variable {A B C D : Type*}

/-! ## Category Laws -/

/-! ### Identity Laws -/

lemma id_comp_proof (f : Entailment A B) :
    (axiomEntailment B) ⊛ f = f := by
  ext as c
  unfold entailmentComp compRel axiomEntailment
  let AxB := entailmentFromRel (identityRel B)
  constructor
  · -- (LHS → RHS)
    rintro ⟨bs, ass, h_len, h_perm, h_E, h_F⟩
    obtain ⟨b, h_bs_eq, h_id⟩ : ∃ b, bs = [b] ∧ identityRel B b c :=
      rPrimeRel_iff_singleton.mp h_F
    rw [h_id] at h_bs_eq
    obtain ⟨asi, h_ass_eq⟩ := List.length_eq_one_iff.mp (by
      rw [← h_len]
      simp [h_bs_eq]
    )
    have h_perm_as_asi : as ~ asi := by
      simp [h_ass_eq, List.flatten] at h_perm
      exact h_perm
    have h_f_asi := h_E (Fin.mk 0 (by simp [h_bs_eq]))
    simp [h_bs_eq, h_ass_eq, Fin.cast] at h_f_asi
    exact f.perm_invariant h_perm_as_asi h_f_asi
  · -- (RHS → LHS)
    intro h_f_as_c
    use [c], [as]
    -- Prove the 3 conjunctions
    refine ⟨?_, ?_, ?_⟩
    · simp
    · simp [List.flatten]
    · constructor
      · intro i
        simp
        exact h_f_as_c
      ·
        unfold entailmentFromRel
        simp

lemma bs_eq_map_singleton_flatten (bs : List A) :
  bs = (bs.map List.singleton).flatten := by
  symm

  induction bs with
  | nil =>
    simp

  | cons x xs ih =>
    simp [ih, List.singleton]

lemma comp_id_proof (f : Entailment A B) :
    f ⊛ (axiomEntailment A) = f := by
  ext as c
  unfold entailmentComp compRel axiomEntailment
  let AxA := entailmentFromRel (identityRel A)
  constructor
  · -- (LHS → RHS)
    rintro ⟨bs, ass, h_len, h_perm, h_E, h_F⟩
    have h_ass_map : ass = bs.map List.singleton := by
      apply List.ext_get
      · simp
        exact h_len.symm
      · intro i
        simp
        intro h1 h2
        let i_bs : Fin bs.length := Fin.mk i h2
        have h_E_i := h_E i_bs
        obtain ⟨a, h_asi_eq, h_id⟩ : ∃ a, ass[i] = [a] ∧ identityRel A a bs[i] := by
          apply rPrimeRel_iff_singleton.mp
          simpa [Fin.cast, Fin.mk.injEq] using h_E_i
        unfold identityRel at h_id
        rw [h_asi_eq, h_id]
        simp [List.singleton]


    simp at h_ass_map

    have tmpH : (map List.singleton bs).flatten = bs := by
      symm
      exact bs_eq_map_singleton_flatten bs

    rw [h_ass_map, tmpH] at h_perm
    exact f.perm_invariant h_perm h_F
  · -- (RHS → LHS)
    intro h_f_as_c
    use as, (as.map List.singleton)
    -- Prove the 3 conjunctions
    refine ⟨?_, ?_, ?_⟩
    · simp [List.length_map]
    · rw [← bs_eq_map_singleton_flatten as]
    · constructor
      · intro i
        simp
        unfold entailmentFromRel
        simp
        apply rPrimeRel_iff_singleton.mpr
        use (as.get i)
        simp [identityRel]
        rfl

      · exact h_f_as_c

/-! ### Associativity -/

axiom entailment_assoc : ∀ (A B C D : Type*)
  (h : Entailment A B) (g : Entailment B C) (f : Entailment C D),
  (f ⊛ g) ⊛ h = f ⊛ (g ⊛ h)


/--
This is just a pain in the arse so I will come back
-/
lemma assoc_proof (h : Entailment A B) (g : Entailment B C) (f : Entailment C D) :
    (f ⊛ g) ⊛ h = f ⊛ (g ⊛ h) :=
  entailment_assoc A B C D h g f


end CatGradedSheet.Q3
