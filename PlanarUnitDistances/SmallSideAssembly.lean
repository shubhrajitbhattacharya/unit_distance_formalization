import PlanarUnitDistances.Algebra
import Mathlib

/-! Deep Blue. Repetition, transposition, and the change of column index
which singles out one torus base column. -/

noncomputable section

namespace PlanarUnitDistances.CartesianGrid

open Fibre

universe u
variable {k I I' J' : Type*} {J : Type u} [Field k]

def Moving (p : I → k × k) (s : J → k × k) (c : I → J → k) : Prop :=
  ∃ (H : I → k × k) (U : J → k × k) (A : I → k) (a : J → k), ∀ i j,
    A i ≠ a j ∧ 2*dot (p i-s j) (H i-U j) = ((c i j)⁻¹-c i j)*(A i-a j)

theorem Moving.reindex {p : I → k × k} {s : J → k × k} {c : I → J → k}
    (M : Moving p s c) (e : I' → I) (f : J' → J) :
    Moving (p ∘ e) (s ∘ f) (fun i j ↦ c (e i) (f j)) := by
  obtain ⟨H,U,A,a,h⟩ := M
  exact ⟨H ∘ e,U ∘ f,A ∘ e,a ∘ f, fun i j ↦ h (e i) (f j)⟩

theorem Moving.transpose {p : I → k × k} {s : J → k × k} {c : I → J → k}
    (M : Moving p s c) : Moving s p (fun j i ↦ c i j) := by
  obtain ⟨H,U,A,a,h⟩ := M
  refine ⟨U,H,fun j ↦ -a j,fun i ↦ -A i,?_⟩
  intro j i
  obtain ⟨h₁,h₂⟩ := h i j
  refine ⟨fun he ↦ h₁ (neg_injective he).symm,?_⟩
  simp only [dot,Prod.fst_sub,Prod.snd_sub] at h₂ ⊢
  linear_combination h₂

theorem repeated [CharZero k] (p : I → k × k) (s : J → k × k) (c : I → J → k)
    (j₀ : J) (hr : ∀ j, s j = s j₀) (hc : ∀ i j, c i j = c i j₀)
    (hne : ∀ i, c i j₀ ≠ 0)
    (hd : ∀ i, chordSq (p i) (s j₀) = 2-c i j₀-(c i j₀)⁻¹) : Moving p s c := by
  classical
  have hrow (i : I) : ∃ H : k × k, 2*dot (p i-s j₀) H = (c i j₀)⁻¹-c i j₀ := by
    let z := c i j₀
    by_cases hx : (p i).1-(s j₀).1=0
    · by_cases hy : (p i).2-(s j₀).2=0
      · have hh := hd i
        simp [chordSq,hx,hy] at hh
        have hm : z*z⁻¹=1 := mul_inv_cancel₀ (hne i)
        have hz : (z⁻¹-z)^2=0 := by
          change 0=2-z-z⁻¹ at hh
          linear_combination (2+z+z⁻¹)*hh-4*hm
        refine ⟨0,?_⟩
        change 2*dot (p i-s j₀) 0 = z⁻¹-z
        rw [eq_zero_of_pow_eq_zero hz]
        simp [dot]
      · refine ⟨(0,(z⁻¹-z)/(2*((p i).2-(s j₀).2))),?_⟩
        simp only [dot,Prod.fst_sub,Prod.snd_sub,mul_zero,zero_add]
        change 2*(_*((z⁻¹-z)/(2*_)))=z⁻¹-z
        field_simp <;> ring
    · refine ⟨((z⁻¹-z)/(2*((p i).1-(s j₀).1)),0),?_⟩
      simp only [dot,Prod.fst_sub,Prod.snd_sub,mul_zero,add_zero]
      change 2*(_*((z⁻¹-z)/(2*_)))=z⁻¹-z
      field_simp <;> ring
  choose H hH using hrow
  refine ⟨H,fun _ ↦ 0,fun _ ↦ 1,fun _ ↦ 0,?_⟩
  intro i j
  refine ⟨one_ne_zero,?_⟩
  simpa only [sub_zero,mul_one,hr j,hc i j] using hH i

theorem small_columns [Fintype J] [Nonempty J] [CharZero k]
    (p : I → k × k) (s : J → k × k) (c : I → J → k) (hl : Fintype.card J ≤ 4)
    (same : ∀ i j j', s j=s j' → c i j=c i j')
    (hne : ∀ i j, c i j≠0)
    (hd : ∀ i j, chordSq (p i) (s j)=2-c i j-(c i j)⁻¹)
    (distinct : ∀ (J' : Type u) [Fintype J'] (e : Option J' ≃ J), Fintype.card (Option J') ≤ 4 →
      ∀ j j', s (e j) ≠ s (e j') → Moving p (s ∘ e) (fun i j ↦ c i (e j))) :
    Moving p s c := by
  classical
  let j₀ := Classical.choice (inferInstance : Nonempty J)
  by_cases h : ∀ j, s j=s j₀
  · exact repeated p s c j₀ h (fun i j ↦ same i j j₀ (h j)) (fun i ↦ hne i j₀) (fun i ↦ hd i j₀)
  obtain ⟨j,hj⟩ := Classical.not_forall.mp h
  let T := {j : J // j ≠ j₀}
  let e : Option T ≃ J := ((Equiv.optionSubtype j₀).symm (Equiv.refl T)).1
  have hc : Fintype.card (Option T) ≤ 4 := (Fintype.card_congr e).trans_le hl
  have M := distinct T e hc (e.symm j) (e.symm j₀) (by simpa only [e.apply_symm_apply] using hj)
  simpa only [Function.comp_def,e.apply_symm_apply,id_eq] using M.reindex id e.symm

end PlanarUnitDistances.CartesianGrid
