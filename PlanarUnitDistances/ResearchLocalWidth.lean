import PlanarUnitDistances.ResearchThresholds
import PlanarUnitDistances.GeometricLargeProfile

namespace PlanarUnitDistances.ResearchPhysical
open OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open OAI.PlanarUnitDistances.ThresholdProfiles CommonFieldModel Finset MeasureTheory
open UniformNormalization EdgeHeightScale NumberField
open scoped Classical
noncomputable section
variable {P Q : Finset Competition.Plane}

private theorem member (p : P) (q : Q) : p∈unitRows P Q q ↔ dist p.val q.val=1 := by
  simp [unitRows,unitNeighbors]

/-- Equality at every local absolute value, with the research graph's
actual symmetric integration window. -/
theorem local_width_eq (M : Model P Q) (he : 0 < incidences P Q) (v : AbsoluteValue M.field ℝ) :
    (toPiece M).localWidth (fun x => v x)=
      let r := profileRadius (unitRows P Q) M.z M.w
      minorityIntegral (fun x : P×Q => weight (unitRows P Q) (incidences P Q) x.1 x.2) (direction (unitRows P Q) M.z)
        (fun w => -r w) r v := by
  let r := profileRadius (unitRows P Q) M.z M.w
  have pos : 0<((toPiece M).E.card:ℝ) := by rwa [Competition.IncidencePiece.Research.edge_count _ (full M)]
  have within e (h : e∈(toPiece M).E) : |(toPiece M).threshold (fun a => v a) e|≤r v := by
    obtain ⟨p,q⟩ := e
    obtain ⟨pq,d⟩ := Finset.mem_filter.mp h
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp pq
    let a : P := ⟨p,hp⟩
    let b : Q := ⟨q,hq⟩
    have ab := (radius_bounds (unitRows P Q) M.z M.w v).1 (a,b)
    change |-Real.log (v ((toPiece M).Z a-(toPiece M).Z b))|≤r v
    rw [z_point,z_center]
    simpa only [threshold,direction,if_pos ((member a b).mpr d)] using ab
  rw [←Competition.IncidencePiece.window_width _ pos _ (-r v) (r v)
    (fun e h => (abs_le.mp (within e h)).1) (fun e h => (abs_le.mp (within e h)).2)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  rw [frequency_at_level]
  have wt : weight (unitRows P Q) (incidences P Q)=fun x q =>
      if dist x.val q.val=1 then (incidences P Q)⁻¹ else 0 := by
    funext p q; simp only [weight,member]
  have th : threshold v (direction (unitRows P Q) M.z)=fun x : P×Q =>
      if dist x.1.val x.2.val=1 then -Real.log (v (M.z (.inl x.1)-M.z (.inr x.2))) else 0 := by
    funext x
    by_cases h : dist x.1.val x.2.val=1 <;> simp [threshold,direction,member,h]
  simp only [wt,th]


end
end PlanarUnitDistances.ResearchPhysical
