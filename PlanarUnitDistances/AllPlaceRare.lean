import PlanarUnitDistances.ArithmeticShift
import PlanarUnitDistances.RecordBudget
import PlanarUnitDistances.PhysicalWindow

namespace PlanarUnitDistances.Competition.IncidencePiece
open Finset MeasureTheory NumberField Real Set
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

/-- Use the genuine arithmetic coordinate records and the standard
normalized local weights on a finite collection of places. -/
def placeIntegral (M : IncidencePiece K) (F : Finset (FinitePlace K))
    (l h : AbsoluteValue K ℝ → ℝ) (u : InfinitePlace K → ℝ)
    (f : CoordinateLevel M.Label → ℝ) : ℝ :=
  ((∑v : InfinitePlace K,(v.mult:ℝ)*(∫s in Icc (l v.val) (h v.val),f (archRecord M v (u v,u v) (u v,u v) s)))+
  (∑v∈F,∫s in Icc (l v.val) (h v.val),f (finiteRecord M v s)))/(Module.finrank ℚ K:ℝ)

private lemma aggregate (M : IncidencePiece K) (F : Finset (FinitePlace K)) (l h : AbsoluteValue K ℝ → ℝ)
    (u : InfinitePlace K → ℝ) (c : ℝ) (hc : 0≤c) (f : CoordinateLevel M.Label → ℝ)
    (bound : ∀r,M.goodRare r → f r≤c*(M.minorityMass r+M.inconsistentMass r)) :
    M.placeIntegral F l h u (M.masked f) ≤
    c*(M.placeIntegral F l h u M.minorityMass+M.placeIntegral F l h u M.inconsistentMass) := by
  let A (f : CoordinateLevel M.Label → ℝ) (v : InfinitePlace K) :=
    ∫s in Icc (l v.val) (h v.val),f (archRecord M v (u v,u v) (u v,u v) s)
  let B (f : CoordinateLevel M.Label → ℝ) (v : FinitePlace K) :=
    ∫s in Icc (l v.val) (h v.val),f (finiteRecord M v s)
  have ha (v : InfinitePlace K) : A (M.masked f) v≤c*(A M.minorityMass v+A M.inconsistentMass v) :=
    integrate_recordwise _ M _ f hc bound
  have hb (v : FinitePlace K) : B (M.masked f) v≤c*(B M.minorityMass v+B M.inconsistentMass v) :=
    integrate_recordwise _ M _ f hc bound
  have a := sum_le_sum (s:=univ) (fun (v : InfinitePlace K) _ => mul_le_mul_of_nonneg_left (ha v) (Nat.cast_nonneg v.mult))
  have b := sum_le_sum (s:=F) (fun v _ => hb v)
  have a' : (∑v : InfinitePlace K,(v.mult:ℝ)*A (M.masked f) v) ≤
      c*((∑v : InfinitePlace K,(v.mult:ℝ)*A M.minorityMass v)+(∑v : InfinitePlace K,(v.mult:ℝ)*A M.inconsistentMass v)) := by
    apply a.trans_eq
    rw [←sum_add_distrib,mul_sum]; apply sum_congr rfl; intro _ _; ring
  have b' : (∑v∈F,B (M.masked f) v) ≤ c*((∑v∈F,B M.minorityMass v)+(∑v∈F,B M.inconsistentMass v)) := by
    apply b.trans_eq
    rw [←sum_add_distrib,mul_sum]
  exact (div_le_div_of_nonneg_right (add_le_add a' b') (Nat.cast_nonneg (Module.finrank ℚ K))).trans_eq (by unfold placeIntegral; dsimp only [A,B]; ring)

/-- For any intervals containing all edge thresholds and any finite set
of finite places containing those with a nonzero edge threshold, one
set of actual archimedean shifts and one dominant-label rule have both
asserted coincidence bounds at the original scale. -/
theorem physical_rare (M : IncidencePiece K) {t : ℝ} (reg : Regular M t) (ht : 0<t)
    (hx : t^(-150*savingG)≤(2:ℝ)^(-154:ℝ)) (hS : 4≤M.scale)
    (F : Finset (FinitePlace K)) (active : ∀v∉F,∀e∈M.E,M.threshold v e=0)
    (l h : AbsoluteValue K ℝ → ℝ)
    (lo : ∀(v : AbsoluteValue K ℝ) e,e∈M.E → l v≤M.threshold v e)
    (hi : ∀(v : AbsoluteValue K ℝ) e,e∈M.E → M.threshold v e≤h v) :
    ∃ (u : InfinitePlace K → ℝ) (d : CoordinateLevel M.Label → M.Label),
      (∀v,u v∈Ioo (0:ℝ) 1) ∧ (∀r,M.goodRare r →
      M.pointMass (fun p => r.selected p≠d r)+M.centerMass (fun q => r.selected q≠d r)
       ≤2*(M.minorityMass r+M.inconsistentMass r)) ∧
      M.placeIntegral F l h u M.minorityMass=M.scale ∧
      M.placeIntegral F l h u M.inconsistentMass≤2*sqrt 2 ∧
      M.placeIntegral F l h u (M.masked fun r => M.edgeException r (d r))≤5*(2:ℝ)^(-144:ℝ)*M.scale ∧
      M.placeIntegral F l h u (M.masked fun r => M.walkException r (d r))≤(2:ℝ)^(-144:ℝ)*M.scale := by
  have he : 0<(M.E.card:ℝ) := (rpow_pos_of_pos ht _).trans_le reg.size
  choose u hu small using fun v : InfinitePlace K => arch_shift M he v (l v.val) (h v.val)
  have e0 := recordwise_rare (L:=M.Label) M reg ht hx
  obtain ⟨d,hd⟩ := e0
  have finite_zero (v : FinitePlace K) : (∫s in Icc (l v.val) (h v.val),M.inconsistentMass (finiteRecord M v s))=0 :=
    integral_eq_zero_of_ae (ae_restrict_of_ae (finite_inconsistent_ae M v))
  have bad : M.placeIntegral F l h u M.inconsistentMass≤2*sqrt 2 := by
    unfold placeIntegral
    simp_rw [finite_zero]
    simp only [sum_const_zero,add_zero]
    apply (div_le_iff₀ (Nat.cast_pos.mpr (Module.finrank_pos (R:=ℚ) (M:=K)))).mpr
    exact (sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (small v) (Nat.cast_nonneg v.mult))).trans_eq
      (by rw [←sum_mul,←Nat.cast_sum,InfinitePlace.sum_mult_eq,mul_comm])
  have av (v : InfinitePlace K) : (∫s in Icc (l v.val) (h v.val),M.minorityMass (archRecord M v (u v,u v) (u v,u v) s))=M.localWidth v := by
    simp_rw [arch_minority M he]
    exact window_width M he v _ _ (lo v.val) (hi v.val)
  have fv (v : FinitePlace K) : (∫s in Icc (l v.val) (h v.val),M.minorityMass (finiteRecord M v s))=M.localWidth v := by
    simp_rw [finite_minority M he]
    exact window_width M he v _ _ (lo v.val) (hi v.val)
  have correct : M.placeIntegral F l h u M.minorityMass=M.scale := by
    unfold placeIntegral scale
    simp_rw [av,fv]
    congr 2
    symm
    apply finsum_eq_sum_of_support_subset
    intro v hv
    by_contra hn
    exact hv (width_zero M he v (active v hn))
  have bd : M.placeIntegral F l h u M.minorityMass+M.placeIntegral F l h u M.inconsistentMass≤2*M.scale := by
    rw [correct]; nlinarith only [bad,hS,sq_sqrt (by norm_num : (0:ℝ)≤2),sq_nonneg (sqrt 2-2)]
  refine ⟨u,d,hu,fun r hr => (hd r hr).1,correct,bad,?_,?_⟩
  · have b := aggregate M F l h u (5*(2:ℝ)^(-144:ℝ)/2) (by positivity)
      (fun r => M.edgeException r (d r)) (fun r hr => (hd r hr).2.1)
    exact b.trans ((mul_le_mul_of_nonneg_left bd (by positivity)).trans_eq (by ring))
  · have b := aggregate M F l h u ((2:ℝ)^(-144:ℝ)/2) (by positivity)
      (fun r => M.walkException r (d r)) (fun r hr => (hd r hr).2.2)
    exact b.trans ((mul_le_mul_of_nonneg_left bd (by positivity)).trans_eq (by ring))

end
end PlanarUnitDistances.Competition.IncidencePiece
