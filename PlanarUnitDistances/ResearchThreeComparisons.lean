import PlanarUnitDistances.ArithmeticWidthTail
import PlanarUnitDistances.ArithmeticMomentReduction
import PlanarUnitDistances.PhysicalWindow
import PlanarUnitDistances.ResearchMomentTransport
import PlanarUnitDistances.ResearchRegularTransport
import PlanarUnitDistances.ResearchScaleEquality
import PlanarUnitDistances.UniformPhysical

namespace PlanarUnitDistances.ResearchPhysical
open OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open CommonFieldModel ProofAssembly Competition NumberField Real Filter
open UniformNormalization EdgeHeightScale
open scoped Topology Classical
noncomputable section

theorem profile_edges_within {P Q : Finset Competition.Plane} (M : Model P Q)
    (v : AbsoluteValue M.field ℝ) (e : Competition.Plane×Competition.Plane) (mem : e∈(toPiece M).E) :
    |(toPiece M).threshold v e|≤profileRadius (unitRows P Q) M.z M.w v := by
  obtain ⟨p,q⟩ := e
  obtain ⟨pq,dist⟩ := Finset.mem_filter.mp mem
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp pq
  let a : P := ⟨p,hp⟩
  let b : Q := ⟨q,hq⟩
  have hmem : a∈unitRows P Q b := by simpa [unitRows,unitNeighbors,a,b] using dist
  change |-Real.log (v ((toPiece M).Z a-(toPiece M).Z b))|≤_
  rw [z_point,z_center]
  simpa only [EdgeHeightScale.threshold,UniformNormalization.direction,ite_eq_left hmem] using
    (radius_bounds (unitRows P Q) M.z M.w v).1 (a,b)

/-- Uniform in the number field as well as the original graph: the
scale and minimum degree thresholds follow from LargePiece for all
sufficiently large real t. Its remaining three premises concern the
same arithmetic records, and its conclusion is the original
ComparisonMoments before deletion or scale selection. -/
theorem eventually_three_comparisons :
    ∀ᶠt : ℝ in atTop, ∀(P Q : Finset Competition.Plane) (M : Model P Q), LargePiece t P Q M →
    ∃(u : InfinitePlace M.field→ℝ)
      (d : IncidencePiece.CoordinateLevel (toPiece M).Label→(toPiece M).Label),
      let G := toPiece M
      let S := pieceScale M
      let F := UniformPhysical.primes (unitRows P Q) M.z M.w
      let h := profileRadius (unitRows P Q) M.z M.w
      let l := fun v => -h v
      let H := G.vertexWidth F l h u d
      let m := G.inconsistentLength F l h u
      (∀v,u v∈Set.Ioo (0:ℝ) 1) ∧
      (∀r,G.goodRare r → G.pointMass (fun p => r.selected p≠d r)+G.centerMass (fun q => r.selected q≠d r)
        ≤2*(G.minorityMass r+G.inconsistentMass r)) ∧
      G.placeIntegral F l h u G.minorityMass=S ∧ G.placeIntegral F l h u G.inconsistentMass≤2*sqrt 2 ∧
      G.placeIntegral F l h u (G.masked fun r => G.edgeException r (d r))≤5*(2:ℝ)^(-144:ℝ)*S ∧
      G.placeIntegral F l h u (G.masked fun r => G.walkException r (d r))≤(2:ℝ)^(-144:ℝ)*S ∧
      (S/203<G.edgeMean (fun e => H e.1) →
      G.placeIntegral F l h u G.commonDisagreement≤2048*(2:ℝ)^(-144:ℝ)*S →
      (∀p∈P,∀q r : Competition.Plane,(p,q)∈G.E → (p,r)∈G.E → q≠r →
        2*H p≤3*(H q+m (p,q)+(H r+m (p,r)))+2*S/eps) →
      ComparisonMoments M) := by
  have gp : 0<savingG := by unfold savingG; positivity [exactGap_pos]
  have gmax := exactGap_lt_largeHeightGap.trans_le (Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1:ℝ)≤2) (by norm_num : -(594036:ℝ)≤ -32))
  have growth : 0<1-90*savingG := by
    norm_num [Real.rpow_neg] at gmax
    unfold savingG; linarith
  have decay : Tendsto (fun t : ℝ => t^(-150*savingG)) atTop (nhds 0) := by
    simpa only [neg_mul] using tendsto_rpow_neg_atTop (show 0<150*savingG by positivity)
  filter_upwards [eventually_gt_atTop (0:ℝ),decay.eventually (eventually_lt_nhds (show 0<(2:ℝ)^(-154:ℝ) by positivity)),
    (tendsto_rpow_atTop growth).eventually_ge_atTop (4/gamma)] with t ht small degrees
  intro P Q M hl
  let G := toPiece M
  have reg := regular_of_large_piece M t hl
  obtain ⟨_,_,_,_,edges,_,_,_,_,_,large⟩ := hl
  have he : 0 < incidences P Q := (Real.rpow_pos_of_pos ht _).trans_le edges
  have scale : G.scale=pieceScale M := scale_eq M he
  have hS : (2:ℝ)^2100<G.scale := scale ▸ large
  have deg (p : Competition.Plane) (hp : p∈G.P) : 2≤G.degreeP p := by
    have floor := (mul_le_mul_of_nonneg_left degrees (by norm_num [gamma] : 0≤gamma/2)).trans (reg.point_degree p hp).1
    rw [show gamma/2*(4/gamma)=2 by norm_num [gamma]] at floor
    exact_mod_cast floor
  let F := UniformPhysical.primes (unitRows P Q) M.z M.w
  let h := profileRadius (unitRows P Q) M.z M.w
  let l := fun v => -h v
  have active (v : FinitePlace M.field) (hv : v∉F) (e) (mem : e∈G.E) : G.threshold v e=0 := by
    have bound := profile_edges_within M v.val e mem
    rw [UniformPhysical.radius_zero _ _ _ hv] at bound
    simpa only [IncidencePiece.threshold,FinitePlace.coe_apply] using abs_nonpos_iff.mp bound
  obtain ⟨u,d,hu,hd,mn,inc,je,jw,finish⟩ := G.physical_scores_of_width_and_common reg ht small.le hS.le F
    active l h (fun v e he => (abs_le.mp (profile_edges_within M v e he)).1)
    (fun v e he => (abs_le.mp (profile_edges_within M v e he)).2)
  refine ⟨u,d,hu,hd,mn.trans scale,inc,?_,?_,?_⟩
  · simpa only [←scale] using je
  · simpa only [←scale] using jw
  · intro mean common pair
    have ξ' : t^(-150*savingG)≤1/(2:ℝ)^72 := small.le.trans (by norm_num)
    have tail := G.arithmetic_width_tail reg ht hS ξ' deg F l h u d hd mn inc
      (by rw [scale]; simpa only [G,F,l,h,toPiece] using pair)
    exact comparison_moments_of_bounds M _
      (finish (by rw [scale]; simpa only [G,F,l,h,IncidencePiece.vertexWidth] using mean) tail
        (by rw [scale]; simpa only [G,F,l,h] using common)) he scale

end
end PlanarUnitDistances.ResearchPhysical
