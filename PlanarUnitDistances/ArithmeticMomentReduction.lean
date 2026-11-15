import PlanarUnitDistances.PhysicalScores
import PlanarUnitDistances.PhysicalError
import PlanarUnitDistances.TailUniformEdge

namespace PlanarUnitDistances.Competition.IncidencePiece
open Real Finset NumberField MeasureTheory
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

/-- The manuscript's equality E[H_p+H_r]=2X, on the very same
shifts, dominant-label rule, arithmetic place integral, and edge law. -/
theorem arithmetic_width_mean (M : IncidencePiece K) (F : Finset (FinitePlace K))
    (l h : AbsoluteValue K ℝ→ℝ) (u : InfinitePlace K→ℝ) (d : CoordinateLevel M.Label→M.Label) :
    M.walkLinear (M.arithmeticScores F l h u d).width =
    2*M.edgeMean (fun e => M.placeIntegral F l h u (M.endpointWidth d e.1)) := by
  let H (p : Plane) := M.placeIntegral F l h u (M.endpointWidth d p)
  obtain ⟨first,second⟩ := M.leg_means H
  change (∑v : Triple M, M.mass v*(H v.1.val+H v.2.2.val))=2*M.edgeMean (fun e => H e.1)
  simp_rw [mul_add]
  rw [sum_add_distrib,first,second,two_mul]

/-- The residual conditions on these explicit scores are the lower mean,
the upper width tail, and the common-level disagreement. All use this
same original graph, its arithmetic shifts, and its chosen dominant label. -/
theorem physical_scores_of_width_and_common (M : IncidencePiece K) {t : ℝ} (reg : Regular M t) (ht : 0<t)
    (hx : t^(-150*savingG)≤(2:ℝ)^(-154:ℝ)) (hS : (2:ℝ)^2100≤M.scale)
    (F : Finset (FinitePlace K)) (active : ∀v∉F,∀e∈M.E,M.threshold v e=0)
    (l h : AbsoluteValue K ℝ → ℝ)
    (lo : ∀(v : AbsoluteValue K ℝ) e,e∈M.E → l v≤M.threshold v e)
    (hi : ∀(v : AbsoluteValue K ℝ) e,e∈M.E → M.threshold v e≤h v) :
    ∃(u : InfinitePlace K→ℝ) (d : CoordinateLevel M.Label→M.Label),
      (∀v,u v∈Set.Ioo (0:ℝ) 1) ∧
      (∀r,M.goodRare r → M.pointMass (fun p => r.selected p≠d r)+M.centerMass (fun q => r.selected q≠d r)
        ≤2*(M.minorityMass r+M.inconsistentMass r)) ∧
      M.placeIntegral F l h u M.minorityMass=M.scale ∧
      M.placeIntegral F l h u M.inconsistentMass≤2*sqrt 2 ∧
      M.placeIntegral F l h u (M.masked fun r => M.edgeException r (d r))≤5*(2:ℝ)^(-144:ℝ)*M.scale ∧
      M.placeIntegral F l h u (M.masked fun r => M.walkException r (d r))≤(2:ℝ)^(-144:ℝ)*M.scale ∧
      let S := M.arithmeticScores F l h u d
      (M.scale/203 < M.edgeMean (fun e => M.placeIntegral F l h u (M.endpointWidth d e.1))) →
      M.walkLinear (fun x => if 8*M.scale/eps<S.width x then S.width x else 0)≤(2:ℝ)^14/2^144*M.scale →
      M.placeIntegral F l h u M.commonDisagreement≤2048*(2:ℝ)^(-144:ℝ)*M.scale →
      MomentBounds M S := by
  obtain ⟨u,d,hu,hd,correct,inc,je,jw,error⟩ := physical_error_mean M reg ht hx hS F active l h lo hi
  refine ⟨u,d,hu,hd,correct,inc,je,jw,?_⟩
  dsimp only
  intro mean tail common
  obtain ⟨hn,en⟩ := arithmeticScores_nonneg M F l h u d
  have comp := physical_endpoints M F active l h lo hi u d
  have large : 2*M.scale/203 < M.walkLinear (M.arithmeticScores F l h u d).width := by
    rw [arithmetic_width_mean]; linarith only [mean]
  refine ⟨fun x => add_nonneg (hn x.1) (hn x.2.2),en,large,tail,?_,
    fun x hp => (comp x hp).1,fun x hp => (comp x hp).2⟩
  exact (error common).2.le.trans_eq (by norm_num)

end
end PlanarUnitDistances.Competition.IncidencePiece
