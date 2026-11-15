import PlanarUnitDistances.GenericNormalizedGrid
import PlanarUnitDistances.SmoothRowObstruction
import PlanarUnitDistances.CurveProjectionDegrees

namespace PlanarUnitDistances.Competition.GenericCurvePoint.NormalizedRow
open MvPolynomial GridElimination LiftedTangent FourRowObstruction SmoothCurveOrders
noncomputable section

variable {E : Type} [Field E] [Algebra ℂ E] [IsAlgClosed E] {y : LiftCoord → E}

def anchorZ (R : NormalizedRow y) (j : Fin 4) : R.K := ⟨_,R.anchor j 0⟩
def anchorW (R : NormalizedRow y) (j : Fin 4) : R.K := ⟨_,R.anchor j 1⟩

theorem anchor_independence (R : NormalizedRow y)
    (ind : AlgebraicIndependent ℂ (fun s : Slot ↦ nullPos y s 0)) :
    AlgebraicIndependent ℂ R.anchorZ :=
  AlgebraicIndependent.of_comp R.K.val (ind.comp Sum.inr Sum.inr_injective)

theorem anchors_on_curve (R : NormalizedRow y) {f g : Poly₂} (data : Data f g y) (j : Fin 4) :
    aeval ![R.anchorZ j,R.anchorW j] g=0 := by
  apply R.K.val.injective
  change R.K.val (aeval ![R.anchorZ j,R.anchorW j] g)=0
  rw [comp_aeval_apply]
  have eq : (fun d ↦ R.K.val (![R.anchorZ j,R.anchorW j] d))=nullPos y (.inr j) := by
    funext d; fin_cases d <;> rfl
  rw [eq]
  exact data.anchor_curve j

private theorem null_dot {L : Type*} [Field L] (I : L) (hI : I^2= -1)
    (x y a b H J U V : L) :
    ((x-I*y)-(a-I*b))*((H+I*J)-(U+I*V))+((x+I*y)-(a+I*b))*((H-I*J)-(U-I*V))=
    2*((x-a)*(H-U)+(y-b)*(J-V)) := by
  linear_combination -2*(y-b)*(J-V)*hI

/-- All curve cases can share this conversion: the orders are on a subfield
of the particular solution field and the roots and tangent come from the
original lifted equations and their normalized velocities. -/
theorem excludes_of_orders (R : NormalizedRow y) {f g : Poly₂} (data : Data f g y)
    (orders : ∃ M : IntermediateField R.K E,
      nullPos y (.inl R.i) 0 ∈ M ∧ nullPos y (.inl R.i) 1 ∈ M ∧ ∃ D : Fin 4 → Mˣ,
      PrivateOrders D ∧ ∀ j, let l := (nullPos y (.inl R.i) 0-algebraMap R.K E (R.anchorZ j))*
                                    (nullPos y (.inl R.i) 1-algebraMap R.K E (R.anchorW j))
                            (((D j : M) : E))=l*(l-4)) : False := by
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℂ E).injective
  let I := algebraMap ℂ E Complex.I
  let v (j : Fin 4) (d : Fin 2) : R.K := ⟨_,R.velocity j d⟩
  let uz (j : Fin 4) := v j 0+algebraMap ℂ R.K Complex.I*v j 1
  let uw (j : Fin 4) := v j 0-algebraMap ℂ R.K Complex.I*v j 1
  let scalar (j : Fin 4) : R.K := ⟨_,R.scalar j⟩
  have hI : I^2= -1 := by dsimp [I]; rw [← map_pow,Complex.I_sq,map_neg,map_one]
  apply excludes_null_tangent _ _ R.anchorZ R.anchorW orders (u y R.i) (μ y R.i)
    (data.inverse R.i) ?_ uz uw scalar (R.h R.i 0+I*R.h R.i 1) (R.h R.i 0-I*R.h R.i 1)
    (R.t R.i) (fun j ↦ (R.tangent R.i j).2) ?_
  · intro j
    exact (chordSq_eq_null y R.i j).symm.trans (data.chord R.i j)
  · intro j
    change (nullPos y (.inl R.i) 1-nullPos y (.inr j) 1)*
      ((R.h R.i 0+I*R.h R.i 1)-(R.v j 0+I*R.v j 1))+
      (nullPos y (.inl R.i) 0-nullPos y (.inr j) 0)*
      ((R.h R.i 0-I*R.h R.i 1)-(R.v j 0-I*R.v j 1))=_
    obtain ⟨pz,pw⟩ := recover y (.inl R.i)
    obtain ⟨az,aw⟩ := recover y (.inr j)
    rw [←pz,←pw,←az,←aw]
    exact (null_dot I hI _ _ _ _ _ _ _ _).trans (R.tangent R.i j).1

/-- Direct exclusion of a normalized row for the given plane-curve pair,
unless the curves coincide up to a scalar and their vertical degree is one. -/
theorem excludes_smooth (R : NormalizedRow y) {f g : Poly₂} (data : Data f g y)
    (pair : CurvePair f g) (ind : AlgebraicIndependent ℂ (fun s : Slot ↦ nullPos y s 0))
    (cases : ¬g∣f ∨ 2≤f.degreeOf 1) : False := by
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℂ E).injective
  letI := R.closed
  obtain ⟨hf,_,fp⟩ := pair.1 f (Or.inl rfl)
  obtain ⟨hg,_,gp⟩ := pair.1 g (Or.inr rfl)
  obtain ⟨_,fd⟩ := BivariateCurveCoordinates.degrees_of_projections f hf fp
  obtain ⟨gz,gw⟩ := BivariateCurveCoordinates.degrees_of_projections g hg gp
  apply R.excludes_of_orders data
  apply orders_on_plane_curves f g hf hg fd gz gw cases _ _ R.transcendental ?_
    R.anchorZ R.anchorW (R.anchor_independence ind) (R.anchors_on_curve data)
  have eq : ![nullPos y (.inl R.i) 0,nullPos y (.inl R.i) 1]=nullPos y (.inl R.i) := by
    funext d; fin_cases d <;> rfl
  rw [eq]
  exact data.row_curve R.i

end
end PlanarUnitDistances.Competition.GenericCurvePoint.NormalizedRow
