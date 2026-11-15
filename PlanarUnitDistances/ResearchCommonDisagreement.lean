import PlanarUnitDistances.PhysicalError
import PlanarUnitDistances.ResearchPhysicalModel
import PlanarUnitDistances.UniformIncidenceLaw
import PlanarUnitDistances.GeometricHeightLaw

namespace PlanarUnitDistances.Competition.IncidencePiece
open Finset NumberField
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]


end
end PlanarUnitDistances.Competition.IncidencePiece

namespace PlanarUnitDistances.ResearchPhysical
open Finset OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open CommonFieldModel FiniteLaw FiniteStarCoupling StarScore UniformPhysical
open UniformNormalization EdgeHeightScale BoundedHeight
open scoped Classical
noncomputable section
variable {P Q : Finset Competition.Plane}

abbrev incidenceLaw (P Q : Finset Competition.Plane) (he : 0 < incidences P Q) :=
  edgeLaw (unitRows P Q) (incidences P Q) he (unitRows_total P Q)

/-- The probability of each physical triple factors into the actual center
marginal and its two posterior neighbor probabilities, including repeated points. -/
theorem atom_at_center (M : Model P Q) (he : 0 < incidences P Q)
    (q : Q) (hq : 0 < degree P q) (p r : P) :
    let π := incidenceLaw P Q he
    (toPiece M).mass (p,q,r) = (right π).val q * ((col π q).val p * (col π q).val r) := by
  let π := incidenceLaw P Q he
  have right_eq : (right π).val q = degree P q / incidences P Q := by
    rw [edge_right]; simp only [centerLaw,unitRows_center_degree]
  have pos := right_eq.symm ▸ div_pos hq he
  change _ = (right π).val q * ((col π q).val p * (col π q).val r)
  rw [col_val π pos p,col_val π pos r,right_eq]
  apply (Competition.IncidencePiece.Research.atom (toPiece M) (full M) p r q).trans
  change (if dist p.val q.val=1 ∧ dist r.val q.val=1 then
    (incidences P Q * degree P q)⁻¹ else 0) = _ * ((weight (unitRows P Q) (incidences P Q) p q / _) *
                                                    (weight (unitRows P Q) (incidences P Q) r q / _))
  have mem (x : P) : x ∈ unitRows P Q q ↔ dist x.val q.val=1 := by simp [unitRows,unitNeighbors]
  by_cases hp : dist p.val q.val=1 <;> by_cases hr : dist r.val q.val=1 <;>
    simp [weight,mem,hp,hr,div_eq_mul_inv] <;> field_simp [he.ne',hq.ne']

/-- At a common level the physical disagreement is exactly the conditional
variation used in the posterior estimates on the original edge law. -/
theorem common_disagreement_eq (M : Model P Q) (he : 0 < incidences P Q)
    (hq : ∀ q : Q, 0 < degree P q)
    (b : Competition.IncidencePiece.CoordinateLevel (toPiece M).Label) :
    (toPiece M).commonDisagreement b =
      if Competition.eps ≤ (toPiece M).minorityMass b then
        VQ (incidenceLaw P Q he) (fun p q => b.bit (p.val,q.val)) else 0 := by
  let π := incidenceLaw P Q he
  unfold Competition.IncidencePiece.commonDisagreement Competition.IncidencePiece.walkLinear
  simp only [LinearMap.coe_mk,AddHom.coe_mk]
  by_cases hc : Competition.eps ≤ (toPiece M).minorityMass b
  · simp only [hc,ite_true,Competition.IncidencePiece.commonBitError]
    unfold VQ avg
    simp_rw [←mismatch]
    simp only [event,avg,pair,Fintype.sum_prod_type,mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro r _
    rw [atom_at_center M he q (hq q) p r]
    have bit_abs (a c : Bool) :
        |Competition.IncidencePiece.bitValue a-Competition.IncidencePiece.bitValue c| =
          if a≠c then (1 : ℝ) else 0 := by
      cases a <;> cases c <;> norm_num [Competition.IncidencePiece.bitValue]
    simp only [bit_abs,mul_assoc]
    split_ifs <;> first | rfl | contradiction
  · simp [Competition.IncidencePiece.commonBitError,hc]

end
end PlanarUnitDistances.ResearchPhysical
