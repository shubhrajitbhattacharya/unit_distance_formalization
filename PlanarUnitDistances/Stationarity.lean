import Mathlib.GroupTheory.CosetCover
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Linear algebra and numerical steps from the section "Height of a stationary ratio".
The linear forms below are the differentials at one point. The arithmetical input
bounding the height of a constant coordinate on an algebraic component is separate. -/

noncomputable section

namespace PlanarUnitDistances

section LinearAlgebra

variable {K V E R : Type*} [Field K] [Infinite K] [AddCommGroup V] [Module K V]

/-- On a prescribed tangent subspace, either one vector moves every ratio, or
one ratio has zero differential on the entire tangent subspace. -/
theorem simultaneous_motion_or_stationarity [Finite E] (T : Submodule K V)
    (dRatio : E → V →ₗ[K] K) :
    (∃ v ∈ T, ∀ e, dRatio e v ≠ 0) ∨ (∃ e, ∀ v ∈ T, dRatio e v = 0) := by
  classical
  by_cases h : ∃ v ∈ T, ∀ e, dRatio e v ≠ 0
  · exact Or.inl h
  · right
    push Not at h
    let f (e : E) := (dRatio e).comp T.subtype
    have hc : (⋃ e, ((f e).ker : Set T)) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro v
      obtain ⟨e, he⟩ := h v v.property
      exact Set.mem_iUnion.mpr ⟨e, he⟩
    obtain ⟨e, he⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hc
    refine ⟨e, fun v hv ↦ ?_⟩
    have hm : (⟨v, hv⟩ : T) ∈ (f e).ker := he.symm ▸ Submodule.mem_top
    exact hm


end LinearAlgebra


/-- With at most four columns, the target row and 3l−4 off-target rows
have at most 24 normalized rectangle parameters and at most 98 variables
after adjoining the gradient multipliers and one output coordinate. -/
theorem small_grid_sizes {l m r : ℕ} (hl : 2 ≤ l) (hl' : l ≤ 4)
    (hm : m ≤ 3 * l - 3) (hr : r ≤ (4 * (m + l) - 2) - 3) :
    m ≤ 9 ∧ (m - 1) * (l - 1) ≤ 24 ∧ (4 * (m + l) - 2) + r + 1 ≤ 98 := by
  have hm' : m ≤ 9 := by omega
  refine ⟨hm', (Nat.mul_le_mul (show m - 1 ≤ 8 by omega) (show l - 1 ≤ 3 by omega)), ?_⟩
  omega


end PlanarUnitDistances
