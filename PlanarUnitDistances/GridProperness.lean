import PlanarUnitDistances.NormalizedSmoothObstruction
import PlanarUnitDistances.RationalRowOrders
import PlanarUnitDistances.ResearchGenericGrid

namespace PlanarUnitDistances.Competition.GenericCurvePoint
open MvPolynomial GridElimination LiftedTangent
noncomputable section

/-- On the full 8 by 4 grid no simultaneous solution over an algebraically
closed extension can have all twelve abscissas independent. Both curve
equations and the four original variables on every edge are retained. -/
theorem no_generic_grid (f g : Poly₂) (pair : CurvePair f g)
    {E : Type} [Field E] [Algebra ℂ E] [IsAlgClosed E] (y : LiftCoord → E)
    (edges : ∀ i,aeval y (edgeList i)=0) (curves : ∀ j,aeval y (curveList f g j)=0)
    (ind : AlgebraicIndependent ℂ (fun s : Slot => nullPos y s 0)) : False := by
  let _ : CharZero E := charZero_of_injective_algebraMap (algebraMap ℂ E).injective
  let data := data_of_lift f g y edges curves
  obtain ⟨R⟩ := normalized_of_lift (pair.1 g (Or.inr rfl)).1.ne_zero data ind
  by_cases smooth : ¬g∣f ∨ 2≤f.degreeOf 1
  · exact R.excludes_smooth data pair ind smooth
  push_neg at smooth
  obtain ⟨hf,_,proj⟩ := pair.1 f (Or.inl rfl)
  have nz := (BivariateCurveCoordinates.degrees_of_projections f hf proj).2
  have one : f.degreeOf 1=1 := by omega
  apply R.excludes_of_orders data
  refine RationalCurveCase.orders_on_rational_row pair smooth.1 one _ _ R.transcendental ?_
    R.anchorZ R.anchorW (R.anchor_independence ind) (R.anchors_on_curve data)
  have eta : ![nullPos y (.inl R.i) 0,nullPos y (.inl R.i) 1]=nullPos y (.inl R.i) := by
    funext j; fin_cases j <;> rfl
  rw [eta]; exact data.row_curve R.i


end
end PlanarUnitDistances.Competition.GenericCurvePoint

namespace PlanarUnitDistances.GridLocus

/-- The manuscript's original affine separating-polynomial formulation. -/
theorem proper_grid_locus : ProperGridLocus := by
  intro f g pair
  by_contra h
  obtain ⟨E,field,alg,closed,y,edges,curves,ind⟩ := generic_of_no_separator f g pair h
  let _ : Field E := field
  let _ : Algebra ℂ E := alg
  let _ : IsAlgClosed E := closed
  exact Competition.GenericCurvePoint.no_generic_grid f g ((pair_equiv _ _).mp pair) y edges curves ind

end PlanarUnitDistances.GridLocus
