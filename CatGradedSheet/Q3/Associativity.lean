import CatGradedSheet.Q3.Composition
import CatGradedSheet.Q3.Defs
import Mathlib.Tactic

open List

namespace CatGradedSheet.Q3

variable {A B C D : Type*}

-- Flattening commutes with grouping
lemma flatten_nested {A : Type*} (asss : List (List (List A))) :
  flatten (flatten asss) = flatten (map flatten asss) := by
  induction asss with
  | nil =>
    simp -- [] = []
  | cons ass tail ih =>
    simp [List.flatten, List.map, List.flatten_append]
    rw [ih]

lemma flatten_singleton {A : Type*} (a : A) :
  flatten [[a]] = [a] := by simp

lemma flatten_concat {A : Type*} (xss yss : List (List A)) :
  flatten (xss ++ yss) = flatten xss ++ flatten yss := by simp

lemma flatten_map_flatten {A : Type*} (xsss : List (List (List A))) :
  flatten (map flatten xsss) = flatten (flatten xsss) := by
  simp [flatten_nested]

lemma perm_flatten {A : Type*} {xss yss : List (List A)} (h : xss ~ yss) :
  flatten xss ~ flatten yss := by
  induction h with
  | nil => simp
  | cons x h_perm ih =>
    simp only [List.flatten]
    apply List.Perm.append_left
    exact ih
  | swap x y zs =>
    apply List.Perm.flatten
    apply List.Perm.swap
  | trans h1 h2 ih1 ih2 =>
    exact List.Perm.trans ih1 ih2

lemma perm_map {A B : Type*} {xs ys : List A} (f : A → B) (h : xs ~ ys) :
  map f xs ~ map f ys := by
  induction h with
  | nil => simp
  | cons x _ ih =>
    simp [List.map]
    exact ih
  | swap x y l =>
    apply List.Perm.map
    apply List.Perm.swap
  | trans _ _ ih1 ih2 =>
    exact List.Perm.trans ih1 ih2


lemma get_flatten {A : Type*} (xss : List (List A)) (i : Fin (length (flatten xss))) :
  ∃ (j : Fin (length xss)) (k : Fin (length (xss.get j))),
    (flatten xss).get i = (xss.get j).get k := by
  induction xss with
  | nil => fin_cases i -- length i is 0 => no get
  | cons head tail ih =>
    let n := head.length
    simp [List.flatten_cons]

    -- Split the proof based on whether i < n or i ≥ n
    if hlt : i.val < n then
      use 0
      use ⟨i.val, hlt⟩
      simp [List.getElem_append_left hlt]
    else
      push_neg at hlt
      have i'_bound : i.val - head.length < tail.flatten.length := by
        have := i.isLt
        simp only [List.flatten_cons, length_append] at this
        omega
      let i' : Fin tail.flatten.length := ⟨i.val - head.length, i'_bound⟩
      obtain ⟨j', k, hk⟩ := ih i'
      use j'.succ, k
      simp only [List.getElem_append_right hlt]
      convert hk using 2


lemma assoc_proof (h : Entailment A B) (g : Entailment B C) (f : Entailment C D) :
    (f ⊛ g) ⊛ h = f ⊛ (g ⊛ h) := by
  ext as d
  unfold entailmentComp compRel
  sorry
end CatGradedSheet.Q3
