import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

namespace Q1

variable {C : Type*} [Category C]

/-!
# Classes of Monomorphisms

This file proves the implications:
  section ⟹ regular ⟹ strong ⟹ extremal

None of these implications is in general an equivalence.
-/

/-! ## Definitions -/

-- Injective / Right inverse?
def IsMonomorphism {X Y: C} (s: X ⟶ Y) : Prop :=
  ∀ (Z : C) (f g : Z ⟶ X), f ≫ s = g ≫ s -> f = g

-- Surjective / left inverse?
def IsEpimorphism {X Y: C} (s: X ⟶ Y) : Prop :=
  ∀ (Z : C) (f g : Y ⟶ Z), s ≫ f = s ≫ g -> f = g

/-- A morphism `s : X → Y` is a section if there exists a retraction `r : Y → X`
    such that `r ∘ s = 𝟙 X`. -/
def IsSection {X Y : C} (s : X ⟶ Y) : Prop :=
  ∃ (r : Y ⟶ X), s ≫ r = 𝟙 X

def IsEqualiser {L X Y: C} (l: L ⟶ X) (f g: X ⟶ Y): Prop :=
  l ≫ f = l ≫ g ∧
  (
    ∀K : C,∀k: K ⟶ X, k ≫ f = k ≫ g
    → ∃!u: K ⟶ L, u ≫ l = k
  )

/-- A morphism `m : X → Y` is a regular monomorphism if it is the equalizer
    of some parallel pair of morphisms. -/
def IsRegularMono {X Y : C} (m : X ⟶ Y) : Prop :=
  ∃ (Z : C) (f g: Y ⟶ Z), IsEqualiser (m) f g

/-- A monomorphism `m : X → Y` is strong if for every commutative square with
    an epimorphism `e : U → V`, there exists a unique diagonal morphism. -/
def IsStrongMono {X Y : C} (m : X ⟶ Y) : Prop :=
  IsMonomorphism m ∧
  ∀ (U V : C) (e : U ⟶ V) (u : U ⟶ X) (v : V ⟶ Y),
    IsEpimorphism e ∧ e ≫ v = u ≫ m -- e is epi, and square commutes
    → ∃! (d: V ⟶ X),
      v = d ≫ m
      ∧ e ≫ d = u

def IsIsomorphism {X Y: C} (f : X ⟶ Y) : Prop :=
  ∃ inv : Y ⟶ X, f ≫ inv = 𝟙 X ∧ inv ≫ f = 𝟙 Y

/-- A monomorphism `m : X → Y` is extremal if for every factorization
    `m = e ≫ v` where `e` is an epimorphism, `e` must be an isomorphism. -/
def IsExtremalMono {X Y : C} (m : X ⟶ Y) : Prop :=
  IsMonomorphism m ∧
  ∀ (V : C) (e : X ⟶ V) (v : V ⟶ Y),
    IsEpimorphism e  -- e is epi
    → m = e ≫ v  -- Triangle comutes
    → IsIsomorphism e -- Is isomophism


/-! ## (1.1) Every section is a monomorphism -/

theorem section_is_mono {X Y : C} {s : X ⟶ Y} (hs : IsSection s) : IsMonomorphism s := by
  obtain ⟨r, hr⟩ := hs
  intro C1 X1 Y1 h
  calc
    X1 = X1 ≫ 𝟙 X := by simp
    _ = X1 ≫ (s ≫ r) := by rw [← hr]
    _ = (X1 ≫ s) ≫ r := by simp [Category.assoc]
    _ = (Y1 ≫ s) ≫ r := by rw [h]
    _ = Y1 ≫ (s ≫ r) := by simp [Category.assoc]
    _ = Y1 ≫ 𝟙 X := by rw [← hr]
    _ = Y1 := by simp


/-! ## (1.2) Every equalizer is a monomorphism -/

theorem equalizer_is_mono {L X Y : C} {l : L ⟶ X} {f g : X ⟶ Y}
    (hl : IsEqualiser l f g) :
    IsMonomorphism l := by
  intro K h1 h2 heq
  obtain ⟨hcomm, huniv⟩ := hl
  have h_eq : (h1 ≫ l) ≫ f = (h1 ≫ l) ≫ g := by
    calc
      (h1 ≫ l) ≫ f = h1 ≫ (l ≫ f) := by simp [Category.assoc]
      _ = h1 ≫ (l ≫ g) := by rw [hcomm]
      _ = (h1 ≫ l) ≫ g := by simp [Category.assoc]
  specialize huniv K (h1 ≫ l) h_eq
  apply ExistsUnique.elim huniv
  intro u hu_prop hu_unique
  have h1_eq_u : h1 = u := hu_unique h1 rfl
  have h2_eq_u : h2 = u := hu_unique h2 heq.symm
  calc
    h1 = u := by rw [h1_eq_u]
    _ = h2 := by rw [← h2_eq_u]

/-! ## (1.3) Every section is a regular monomorphism -/

theorem section_is_regular_mono {X Y : C} {s : X ⟶ Y} (hs : IsSection s) :
    IsRegularMono s := by
  obtain ⟨r, hid⟩ := hs
  use Y, 𝟙 Y, r ≫ s
  constructor
  · calc
    s ≫ 𝟙 Y = s := by simp
    _ = 𝟙 X ≫ s := by simp
    _ = (s ≫ r) ≫ s := by rw [hid]
    _ = s ≫ r ≫ s := by rw [Category.assoc]
  · intros K k a
    have a_simp : k = k ≫ r ≫ s := by simp at a; exact a
    use k ≫ r
    constructor
    · simp
      exact a_simp.symm
    · simp
      intro y yh
      calc
        y = y ≫ 𝟙 X := by simp
        _ = y ≫ (s ≫ r) := by rw [← hid]
        _ = (y ≫ s) ≫ r := by simp [Category.assoc]
        _ = k ≫ r := by rw [yh]




/-! ## (1.4) Every regular monomorphism is strong -/

theorem cancel_epimorphism {A B C : C} (e : A ⟶ B) (h_epi: IsEpimorphism e) (f g : B ⟶ C)
  : e ≫ f = e ≫ g ↔ f = g := by
    constructor
    · apply h_epi
    · intro h_eq
      rw [h_eq]

theorem cancel_monomorphism {A B C : C} (e : B ⟶ C) (h_mono: IsMonomorphism e) (f g : A ⟶ B)
  : f ≫ e = g ≫ e ↔ f = g := by
    constructor
    · apply h_mono
    · intro h_eq
      rw [h_eq]


theorem regular_mono_is_strong {X Y : C} {m : X ⟶ Y} (hm : IsRegularMono m) :
    IsStrongMono m := by
  obtain ⟨w, ⟨f, g, h_is_equaliser⟩⟩ := hm
  have h_mono : IsMonomorphism m := equalizer_is_mono h_is_equaliser
  constructor
  · exact equalizer_is_mono h_is_equaliser
  · intro U V e u v ⟨h_epi, h_comm⟩
    obtain ⟨h_mf_is_mg, h_all_to_uniq⟩ := h_is_equaliser
    have eq_fg : (e ≫ v) ≫ f = (e ≫ v) ≫ g := by
      calc
        (e ≫ v) ≫ f = (u ≫ m) ≫ f := by rw [h_comm]
        _ = u ≫ (m ≫ f) := by simp [Category.assoc]
        _ = u ≫ (m ≫ g) := by rw [h_mf_is_mg]
        _ = (u ≫ m) ≫ g := by simp [Category.assoc]
        _ = (e ≫ v) ≫ g := by rw [← h_comm]
    have v_equalizes : v ≫ f = v ≫ g := by
      apply h_epi
      rewrite [Category.assoc] at eq_fg
      rewrite [Category.assoc] at eq_fg
      exact eq_fg

    specialize h_all_to_uniq V (v)
    obtain ⟨d, hd, hd_unique⟩ := h_all_to_uniq v_equalizes
    use d
    simp
    constructor
    · constructor
      · exact hd.symm
      · have h_with_m : (e ≫ d) ≫ m = u ≫ m := by
          calc
            (e ≫ d) ≫ m = e ≫ (d ≫ m) := by simp [Category.assoc]
            _ = e ≫ v := by rw [hd]
            _ = u ≫ m := by rw [h_comm]
        exact (cancel_monomorphism m h_mono (e ≫ d) u).mp h_with_m
    · intro y h_v_is_ym h_ey_is_u
      have dm_is_ym : d ≫ m = y ≫ m := by
        calc
          d ≫ m = v := by rw [hd]
          _ = y ≫ m := by rw [h_v_is_ym]
      have h1 : d = y := (cancel_monomorphism m h_mono d y).mp dm_is_ym
      exact h1.symm

/-! ## (1.5) Every strong monomorphism is extremal -/

theorem strong_mono_is_extremal {X Y : C} {m : X ⟶ Y} (hm : IsStrongMono m) :
    IsExtremalMono m := by
  obtain ⟨hm_mono, h_old⟩ := hm
  constructor
  · exact hm_mono
  · intro V e v he_epi tri_comm
    specialize h_old X V e (𝟙 X) v
    have conj : IsEpimorphism e ∧ e ≫ v = 𝟙 X ≫ m := by
      constructor
      · exact he_epi
      · simp
        exact tri_comm.symm
    have result := h_old conj
    obtain ⟨d, hd_props, hd_uniq⟩ := result
    obtain ⟨hd1, hd2⟩ := hd_props
    use d
    constructor
    · exact hd2
    · have epiE : e ≫ (d ≫ e) = e ≫ 𝟙 V := by
        calc
          e ≫ (d ≫ e) = (e ≫ d) ≫ e := by simp [Category.assoc]
          _ = 𝟙 X ≫ e := by rw [hd2]
          _ = e := by simp
          _ = e ≫ 𝟙 V := by simp
      have fin : d ≫ e = 𝟙 V := (cancel_epimorphism e he_epi (d ≫ e) (𝟙 V)).mp epiE
      exact fin




/-! ## Summary: The chain of implications -/

theorem section_implies_extremal {X Y : C} {s : X ⟶ Y} (hs : IsSection s) :
    IsExtremalMono s := by
  apply strong_mono_is_extremal
  apply regular_mono_is_strong
  exact section_is_regular_mono hs

end Q1
