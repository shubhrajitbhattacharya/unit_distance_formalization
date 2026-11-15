import PlanarUnitDistances.Algebra
import Mathlib

/-! Sparse row localization by intersecting the spaces of extendible shared
velocities. Logarithmic torus velocities remove all linearized inverse equations. -/

noncomputable section

namespace PlanarUnitDistances.GridLocalization

section Intersections

variable {k V I : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- If every subspace contains `M`, at most `dim U − dim M` of them cut a
starting subspace `U ≥ M` down to its intersection with all the subspaces. -/
theorem select_intersection (F : I → Submodule k V) (M U : Submodule k V)
    (hm : ∀ i, M ≤ F i) (hU : M ≤ U) :
    ∃ S : Finset I, S.card + Module.finrank k M ≤ Module.finrank k U ∧
      ∀ v ∈ U, (∀ i ∈ S, v ∈ F i) → ∀ i, v ∈ F i := by
  classical
  by_cases hall : ∀ i, U ≤ F i
  · exact ⟨∅, by simpa using Submodule.finrank_mono hU, fun v hv _ i ↦ hall i hv⟩
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    have hlt : U ⊓ F i < U := lt_of_le_of_ne inf_le_left (fun he ↦ hi (inf_eq_left.mp he))
    have hd := Submodule.finrank_lt_finrank_of_lt hlt
    obtain ⟨S, hcard, hS⟩ := select_intersection F M (U ⊓ F i) hm (le_inf hU (hm i))
    refine ⟨insert i S, ?_, ?_⟩
    · have hb := Finset.card_insert_le i S
      omega
    · intro v hv hw
      exact hS v ⟨hv, hw i (Finset.mem_insert_self ..)⟩
        (fun j hj ↦ hw j (Finset.mem_insert_of_mem hj))
termination_by Module.finrank k U
decreasing_by exact hd

end Intersections

variable {k I J : Type*} [Field k]

/-- Shared column position velocities, and one log velocity per nonbase column. -/
abbrev Shared (k J : Type*) := ((Option J × Fin 2) → k) × (J → k)

def colLog (b : Shared k J) (j : Option J) : k := j.elim 0 b.2

/-- The unit ratios have fixed quotients, so their logarithmic velocities are
`a − b_j`. The base column log velocity is normalized to zero. -/
def rowEquation (p : I → k × k) (s : Option J → k × k) (R : I → Option J → k)
    (i : I) (u : Fin 3 → k) (b : Shared k J) (j : Option J) : Prop :=
  2 * ((p i).1 - (s j).1) * (u 0 - b.1 (j,0)) +
  2 * ((p i).2 - (s j).2) * (u 1 - b.1 (j,1)) = R i j * (u 2 - colLog b j)

/-- Column velocities admitting a compatible velocity of row `i`. -/
def extendible (p : I → k × k) (s : Option J → k × k) (R : I → Option J → k)
    (i : I) : Submodule k (Shared k J) where
  carrier := {b | ∃ u : Fin 3 → k, ∀ j, rowEquation p s R i u b j}
  zero_mem' := ⟨0, fun j ↦ by cases j <;> simp [rowEquation, colLog]⟩
  add_mem' := by
    rintro b c ⟨u,hu⟩ ⟨v,hv⟩
    refine ⟨u+v, fun j ↦ ?_⟩
    have h₁ := hu j
    have h₂ := hv j
    cases j <;> simp [rowEquation, colLog] at h₁ h₂ ⊢ <;> linear_combination h₁ + h₂
  smul_mem' := by
    rintro a b ⟨u,hu⟩
    refine ⟨a • u, fun j ↦ ?_⟩
    have h := hu j
    cases j <;> simp [rowEquation, colLog] at h ⊢ <;> linear_combination a * h

def sharedRigid (s : Option J → k × k) : (Fin 3 → k) →ₗ[k] Shared k J where
  toFun w := (fun ⟨j,h⟩ ↦ ![w 0 - w 2 * (s j).2, w 1 + w 2 * (s j).1] h, 0)
  map_add' u v := by
    apply Prod.ext
    · funext ⟨j,h⟩; fin_cases h <;> simp <;> ring
    · simp
  map_smul' a u := by
    apply Prod.ext
    · funext ⟨j,h⟩; fin_cases h <;> simp <;> ring
    · simp

theorem sharedRigid_injective (s : Option J → k × k) (j j' : Option J) (hj : s j ≠ s j') :
    Function.Injective (sharedRigid s) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro w hw
  have hx (j : Option J) : w 0 - w 2 * (s j).2 = 0 :=
    congrFun (congrArg Prod.fst hw) (j,0)
  have hy (j : Option J) : w 1 + w 2 * (s j).1 = 0 :=
    congrFun (congrArg Prod.fst hw) (j,1)
  have hrot : w 2 = 0 := by
    by_contra hn
    apply hj
    apply Prod.ext
    · apply mul_left_cancel₀ hn
      linear_combination hy j - hy j'
    · apply mul_left_cancel₀ hn
      linear_combination hx j' - hx j
  have h₀ := hx j
  have h₁ := hy j
  simp only [hrot, zero_mul, sub_zero, add_zero] at h₀ h₁
  funext m
  fin_cases m <;> assumption

theorem rigid_extendible (p : I → k × k) (s : Option J → k × k) (R : I → Option J → k)
    (i : I) : LinearMap.range (sharedRigid s) ≤ extendible p s R i := by
  rintro _ ⟨w,rfl⟩
  refine ⟨![w 0 - w 2 * (p i).2, w 1 + w 2 * (p i).1, 0], fun j ↦ ?_⟩
  cases j <;> simp [rowEquation, sharedRigid, colLog] <;> ring

/-- A target stationary on the full normalized tangent remains stationary on a
subgrid retaining all columns, its own row, and at most `3l−3` rows in total. -/
theorem localize_logarithmic_tangent [Fintype J] [Nontrivial I] (p : I → k × k)
    (s : Option J → k × k) (R : I → Option J → k) (iₑ : I) (jₑ j j' : Option J)
    (hj : s j ≠ s j')
    (stationary : ∀ (b : Shared k J) (u : I → Fin 3 → k),
      (∀ i q, rowEquation p s R i (u i) b q) → u iₑ 2 - colLog b jₑ = 0) :
    ∃ S : Finset I, iₑ ∈ S ∧ 2 ≤ S.card ∧ S.card ≤ 3 * Fintype.card (Option J) - 3 ∧
      ∀ (b : Shared k J) (u : I → Fin 3 → k),
        (∀ i ∈ S, ∀ q, rowEquation p s R i (u i) b q) → u iₑ 2 - colLog b jₑ = 0 := by
  classical
  let M := LinearMap.range (sharedRigid s)
  obtain ⟨T, hcard, hT⟩ := select_intersection (extendible p s R) M ⊤
    (rigid_extendible p s R) le_top
  have hm : Module.finrank k M = 3 := by
    rw [show M = LinearMap.range (sharedRigid s) from rfl,
      LinearMap.finrank_range_of_inj (sharedRigid_injective s j j' hj), Module.finrank_pi]
    simp
  have hdim : Module.finrank k (Shared k J) = 3 * Fintype.card (Option J) - 1 := by
    simp [Shared, Module.finrank_prod]
    omega
  rw [hm, finrank_top, hdim] at hcard
  let V := insert iₑ T
  have heV : iₑ ∈ V := Finset.mem_insert_self ..
  have hV : V.card ≤ 3 * Fintype.card (Option J) - 3 := by
    have := Finset.card_insert_le iₑ T
    change (insert iₑ T).card ≤ _
    omega
  have hl : 2 ≤ Fintype.card (Option J) :=
    Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨j, j', fun he ↦ hj (congrArg s he)⟩⟩
  obtain ⟨S, hVS, hS₂, hSmax⟩ : ∃ S : Finset I, V ⊆ S ∧ 2 ≤ S.card ∧
      S.card ≤ 3 * Fintype.card (Option J) - 3 := by
    by_cases hv : 2 ≤ V.card
    · exact ⟨V, Finset.Subset.rfl, hv, hV⟩
    · obtain ⟨i', hi'⟩ := exists_ne iₑ
      refine ⟨insert i' V, Finset.subset_insert .., ?_, ?_⟩
      · apply Finset.one_lt_card.mpr
        exact ⟨i', Finset.mem_insert_self .., iₑ, Finset.mem_insert_of_mem heV, hi'⟩
      · have := Finset.card_insert_le i' V
        omega
  refine ⟨S, hVS heV, hS₂, hSmax, ?_⟩
  intro b u hu
  have hfull := hT b Submodule.mem_top (fun i hi ↦
    show b ∈ extendible p s R i from ⟨u i, hu i (hVS (Finset.mem_insert_of_mem hi))⟩)
  choose v hv using (show ∀ i, ∃ w, ∀ q, rowEquation p s R i w b q from hfull)
  let v' (i : I) := if i = iₑ then u i else v i
  have hh (i : I) (q : Option J) : rowEquation p s R i (v' i) b q := by
    by_cases he : i = iₑ
    · subst i
      simpa [v'] using hu iₑ (hVS heV) q
    · simpa [v', he] using hv i q
  simpa [v'] using stationary b v' hh

end PlanarUnitDistances.GridLocalization
