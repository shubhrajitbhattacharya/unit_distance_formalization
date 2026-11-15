import PlanarUnitDistances.ResearchFixedPairBudget
import PlanarUnitDistances.ResearchThreeComparisons

namespace PlanarUnitDistances.ResearchPhysical
open OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open CommonFieldModel ProofAssembly Competition NumberField Real Filter
open UniformNormalization EdgeHeightScale
open scoped Topology Classical
noncomputable section

/-- The fixed-pair estimate on the original LargePiece, with the original
profile radius and the very same finite primes, shifts and labels.
Only its point-width lower mean and common-disagreement upper mean remain. -/
theorem eventually_two_comparisons :
    ∀ᶠt : ℝ in atTop, ∀(P Q : Finset Competition.Plane) (M : Model P Q), LargePiece t P Q M →
    ∃(u : InfinitePlace M.field→ℝ)
      (d : IncidencePiece.CoordinateLevel (toPiece M).Label→(toPiece M).Label),
      let G := toPiece M
      let S := pieceScale M
      let F := UniformPhysical.primes (unitRows P Q) M.z M.w
      let h := profileRadius (unitRows P Q) M.z M.w
      let l := fun v => -h v
      let H := G.vertexWidth F l h u d
      (∀v,u v∈Set.Ioo (0:ℝ) 1) ∧
      (∀r,G.goodRare r → G.pointMass (fun p => r.selected p≠d r)+G.centerMass (fun q => r.selected q≠d r)
        ≤2*(G.minorityMass r+G.inconsistentMass r)) ∧
      G.placeIntegral F l h u G.minorityMass=S ∧ G.placeIntegral F l h u G.inconsistentMass≤2*sqrt 2 ∧
      G.placeIntegral F l h u (G.masked fun r => G.edgeException r (d r))≤5*(2:ℝ)^(-144:ℝ)*S ∧
      G.placeIntegral F l h u (G.masked fun r => G.walkException r (d r))≤(2:ℝ)^(-144:ℝ)*S ∧
      (S/203<G.edgeMean (fun e => H e.1) →
       G.placeIntegral F l h u G.commonDisagreement≤2048*(2:ℝ)^(-144:ℝ)*S →
       ComparisonMoments M) := by
  filter_upwards [eventually_three_comparisons,eventually_gt_atTop (0:ℝ)] with t on ht
  intro P Q M hl
  obtain ⟨u,d,hu,hd,hmin,hbad,je,jw,finish⟩ := on P Q M hl
  refine ⟨u,d,hu,hd,hmin,hbad,je,jw,?_⟩
  intro mean common
  apply finish mean common
  intro p _ q r he he' hne
  let G := toPiece M
  let F := UniformPhysical.primes (unitRows P Q) M.z M.w
  let h := profileRadius (unitRows P Q) M.z M.w
  let l := fun v => -h v
  have positive : 0 < incidences P Q := (Real.rpow_pos_of_pos ht _).trans_le hl.2.2.2.2.1
  have scale : G.scale=pieceScale M := scale_eq M positive
  have big : (2:ℝ)^2100<G.scale := by rw [scale]; exact hl.2.2.2.2.2.2.2.2.2.2
  have active (v : FinitePlace M.field) (hv : v∉F) (e) (mem : e∈G.E) : G.threshold v e=0 := by
    have bound := profile_edges_within M v.val e mem
    rw [UniformPhysical.radius_zero _ _ _ hv] at bound
    simpa only [IncidencePiece.threshold,FinitePlace.coe_apply] using abs_nonpos_iff.mp bound
  have result := fixed_pair_width G F active l h
    (fun v e mem => (abs_le.mp (profile_edges_within M v e mem)).1)
    (fun v e mem => (abs_le.mp (profile_edges_within M v e mem)).2)
    u d big (hmin.trans scale.symm) hbad he he' hne
  rw [scale] at result
  exact result

end
end PlanarUnitDistances.ResearchPhysical

