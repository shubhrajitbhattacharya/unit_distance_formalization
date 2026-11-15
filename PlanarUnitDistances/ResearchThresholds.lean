import PlanarUnitDistances.ResearchPhysicalModel
import PlanarUnitDistances.EdgeHeightScale
import PlanarUnitDistances.PhysicalWindow

namespace PlanarUnitDistances.ResearchPhysical
open OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open OAI.PlanarUnitDistances.ThresholdProfiles CommonFieldModel Finset
open scoped Classical
noncomputable section
variable {P Q : Finset Competition.Plane}

private theorem sum_vertices (f : Competition.Plane × Competition.Plane → ℝ) :
    (∑ x : P×Q, f (x.1.val,x.2.val)) = ∑ x∈P×ˢQ,f x := by
  rw [Fintype.sum_prod_type,Finset.sum_product]
  calc ∑ p : P, ∑ q : Q, f (p.val,q.val) =
      ∑ p : P, ∑ q∈Q,f (p.val,q) := sum_congr rfl (fun p _ => Finset.sum_coe_sort Q (fun q => f (p.val,q)))
    _ = _ := Finset.sum_coe_sort P (fun p => ∑ q∈Q,f (p,q))

theorem edgeProb_eq_sum (M : Model P Q) (A : Competition.Plane×Competition.Plane → Prop) :
    (toPiece M).edgeProb A = ∑ x : P×Q,
      if dist x.1.val x.2.val=1 ∧ A (x.1.val,x.2.val) then (incidences P Q)⁻¹ else 0 := by
  let d := incidences P Q
  let h (x : Competition.Plane × Competition.Plane) := dist x.1 x.2=1 ∧ A x
  let f (x : Competition.Plane × Competition.Plane) : ℝ := if h x then d⁻¹ else 0
  change _ = ∑ x : P×Q, f (x.1.val,x.2.val)
  rw [sum_vertices]
  unfold Competition.IncidencePiece.edgeProb
  rw [Competition.IncidencePiece.Research.edge_count _ (full M)]
  change ((((P×ˢQ).filter (fun x => dist x.1 x.2=1)).filter A).card:ℝ)/d=_
  simp only [filter_filter]
  change (((P×ˢQ).filter h).card:ℝ)/d=∑ x∈P×ˢQ,if h x then d⁻¹ else 0
  rw [←sum_filter]
  simp [div_eq_mul_inv]

/-- The exact minority frequency at each place and each real level agrees
in the physical record and the original uniform bipartite graph. -/
theorem frequency_at_level (M : Model P Q) (v : AbsoluteValue M.field ℝ) (s : ℝ) :
    (toPiece M).frequencyMinority (fun x => v x) s =
      minority (fun x : P×Q => if dist x.1.val x.2.val=1 then (incidences P Q)⁻¹ else 0)
        (fun x : P×Q => if dist x.1.val x.2.val=1 then
          -Real.log (v (M.z (.inl x.1)-M.z (.inr x.2))) else 0) s := by
  unfold Competition.IncidencePiece.frequencyMinority minority
  suffices (toPiece M).edgeProb (fun e => s<(toPiece M).threshold (fun x => v x) e)=_ by
    rw [this]
  rw [edgeProb_eq_sum]
  unfold frequency
  apply sum_congr rfl
  intro x _
  rcases x with ⟨p,q⟩
  by_cases h : dist p.val q.val=1
  · by_cases b : s < -Real.log (v (M.z (.inl p)-M.z (.inr q))) <;>
      simp [h,Competition.IncidencePiece.threshold,z_point,z_center,bit,b]
  · simp [h]

end
end PlanarUnitDistances.ResearchPhysical
