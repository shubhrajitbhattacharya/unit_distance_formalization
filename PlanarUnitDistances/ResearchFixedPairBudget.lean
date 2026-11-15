import PlanarUnitDistances.ResearchRareCharge
import PlanarUnitDistances.FixedPairWidth

namespace PlanarUnitDistances.ResearchPhysical
open Competition Competition.IncidencePiece Real NumberField Finset Set MeasureTheory
open OAI.PlanarUnitDistances.BudgetPlaces
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

/-- The fixed-pair rare-only estimate in (budnew-rarealone) for the literal
finite incidence graph, any selected labels, and its actual normalized places.
The prime set need only cover nonzero edge thresholds. -/
theorem fixed_pair_rare_budget (M : IncidencePiece K) (F : Finset (FinitePlace K))
    (active : ∀v∉F,∀e∈M.E,M.threshold v e=0) (l h : AbsoluteValue K ℝ → ℝ)
    (lo : ∀(v : AbsoluteValue K ℝ) e,e∈M.E → l v≤M.threshold v e)
    (hi : ∀(v : AbsoluteValue K ℝ) e,e∈M.E → M.threshold v e≤h v)
    (u : InfinitePlace K→ℝ) (d : CoordinateLevel M.Label→M.Label) {p q r : Competition.Plane}
    (he : (p,q)∈M.E) (he' : (p,r)∈M.E) (hne : q≠r) :
    M.placeIntegral F l h u (M.rarePairScore d p q r)≤2*log 2 := by
  let a := jump M p q
  let b := jump M p r
  have ha : a≠0 := jump_ne M he
  have hb : b≠0 := jump_ne M he'
  have hab : a≠b := distinct_jumps M he he' hne
  let c (v : FinitePlace K) := flankCharge v.val 0 a b
  have fin : (Function.support c).Finite := by
    apply (FinitePlace.hasFiniteMulSupport (differenceProduct_ne_zero hab)).subset
    intro v hv eq
    apply hv
    change flankCharge v.val 0 a b=0
    rw [flankCharge_eq v.val 0 ha hb hab]
    change v (differenceProduct a b)=1 at eq
    change -log (v (differenceProduct a b))+2*0=0
    simp [eq]
  have nonneg (v : FinitePlace K) (hv : v∉F) : 0≤c v := by
    have q0 : OAI.PlanarUnitDistances.BudgetPlaces.threshold v.val a=0 := active v hv _ he
    have r0 : OAI.PlanarUnitDistances.BudgetPlaces.threshold v.val b=0 := active v hv _ he'
    have n := flank_length_nonneg M he he' hne (.inr v)
    change 0≤alpha v.val a b+0 at n
    simp only [c,flankCharge,q0,r0,max_self,min_self,sub_self,sub_zero]
    exact mul_nonneg (by norm_num) n
  have fs : ∑v∈F,c v ≤ ∑ᶠv : FinitePlace K,c v := by
    rw [finsum_eq_sum_of_support_subset c (s:=F∪fin.toFinset) (fun v hv => mem_union_right _ (fin.mem_toFinset.mpr hv))]
    exact sum_le_sum_of_subset_of_nonneg subset_union_left (fun v _ hv => nonneg v hv)
  have here (v : Place K) := local_rare_charge M u v d he he' hne
    (l:=l (valuation v)) (h:=h (valuation v))
    ⟨lo _ _ he,hi _ _ he⟩ ⟨lo _ _ he',hi _ _ he'⟩
  rw [←normalized_flank_charge ha hb hab]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply add_le_add
  · apply sum_le_sum
    intro v _
    exact mul_le_mul_of_nonneg_left (here (.inl v)) (Nat.cast_nonneg _)
  · apply le_trans _ fs
    apply sum_le_sum
    intro v _
    exact here (.inr v)

/-- Actual widths satisfy the inequality required by the tail theorem
without assuming a pair bound. -/
theorem fixed_pair_width (M : IncidencePiece K) (F : Finset (FinitePlace K))
    (active : ∀v∉F,∀e∈M.E,M.threshold v e=0) (l h : AbsoluteValue K ℝ → ℝ)
    (lo : ∀(v : AbsoluteValue K ℝ) e,e∈M.E → l v≤M.threshold v e)
    (hi : ∀(v : AbsoluteValue K ℝ) e,e∈M.E → M.threshold v e≤h v)
    (u : InfinitePlace K→ℝ) (d : CoordinateLevel M.Label→M.Label)
    (hS : (2:ℝ)^2100 < M.scale) (hmin : M.placeIntegral F l h u M.minorityMass=M.scale)
    (hbad : M.placeIntegral F l h u M.inconsistentMass≤2*sqrt 2)
    {p q r : Competition.Plane} (he : (p,q)∈M.E) (he' : (p,r)∈M.E) (hne : q≠r) :
    2*M.vertexWidth F l h u d p ≤ 3*(M.vertexWidth F l h u d q+M.inconsistentLength F l h u (p,q)+
      (M.vertexWidth F l h u d r+M.inconsistentLength F l h u (p,r)))+2*M.scale/eps :=
  M.width_pair_of_rare_score F l h u d hS hmin hbad p q r (fixed_pair_rare_budget M F active l h lo hi u d he he' hne)

end
end PlanarUnitDistances.ResearchPhysical

