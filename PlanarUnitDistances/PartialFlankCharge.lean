import PlanarUnitDistances.FlankCharge
import PlanarUnitDistances.PhysicalLabels

namespace OAI.PlanarUnitDistances.BudgetPlaces
open NumberField Finset Function Real
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

/-- The arithmetic comparison may integrate over a finite set of finite
places chosen before the two neighbors. Their individual directions being
units outside this set suffices, even if their difference is not a unit. -/
theorem partial_flank_charge (F : Finset (FinitePlace K)) {d d' : K} (hd : d≠0) (hd' : d'≠0)
    (hne : d≠d') (outside : ∀v : FinitePlace K,v∉F → v d=1 ∧ v d'=1) :
    ((∑v : InfinitePlace K,(v.mult:ℝ)*flankCharge v.1 (log 2) d d')+
      ∑v∈F,flankCharge v.1 0 d d')/(Module.finrank ℚ K:ℝ) ≤ 2*log 2 := by
  let charge (v : FinitePlace K) := flankCharge v.1 0 d d'
  let y := differenceProduct d d'
  have yne : y≠0 := differenceProduct_ne_zero hne
  have eq (v : FinitePlace K) : charge v= -log (v y) := by
    calc
      _ = -log (v y)+2*0 := flankCharge_eq v.1 0 hd hd' hne
      _ = _ := by ring
  have nonneg (v : FinitePlace K) (hv : v∉F) : 0≤charge v := by
    obtain ⟨a,b⟩ := outside v hv
    change v.1 d=1 at a
    change v.1 d'=1 at b
    have sub (x x' : K) (hx : v.1 x=1) (hx' : v.1 x'=1) : v.1 (x-x')≤1 := by
      have h := PhysicalLabels.nonarch v x (-x')
      simpa only [←sub_eq_add_neg,v.1.map_neg,hx,hx',max_self] using h
    have c : v.1 (d-d')≤1 := sub _ _ a b
    have e : v.1 (d⁻¹-d'⁻¹)≤1 := sub _ _ (by rw [map_inv₀,a,inv_one])
      (by rw [map_inv₀,b,inv_one])
    have vy : v y≤1 := by
      change v.1 ((d-d')*(d⁻¹-d'⁻¹))≤1
      rw [v.1.map_mul]
      simpa only [one_mul] using mul_le_mul c e (v.1.nonneg _) zero_le_one
    rw [eq]
    exact neg_nonneg.mpr (log_nonpos (v.1.nonneg y) vy)
  have finite : (support charge).Finite := by
    apply (FinitePlace.hasFiniteMulSupport yne).subset
    intro v hv
    change v y ≠ 1
    intro h
    exact hv (by simp [eq,h])
  let A := F∪finite.toFinset
  have sup : support charge⊆A := fun v hv =>
    Finset.mem_union_right _ (finite.mem_toFinset.mpr hv)
  have trunc : ∑v∈F,charge v≤∑ᶠv,charge v := by
    rw [finsum_eq_sum_of_support_subset _ sup]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (fun v _ h => nonneg v h)
  exact (div_le_div_of_nonneg_right (add_le_add (le_refl _) trunc)
    (Nat.cast_nonneg _)).trans_eq (normalized_flank_charge hd hd' hne)

end
end OAI.PlanarUnitDistances.BudgetPlaces
