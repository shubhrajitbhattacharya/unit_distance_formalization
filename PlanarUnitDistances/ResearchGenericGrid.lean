import PlanarUnitDistances.EffectiveGridGeometry
import PlanarUnitDistances.GenericGridPoint

namespace PlanarUnitDistances.GridLocus
open MvPolynomial Competition.GridElimination

/-- Failure of the exact manuscript separator gives an extension-field
solution of the concrete lifted equations with twelve independent
abscissas. The separator and the density use the same curve product. -/
theorem generic_of_no_separator (f g : PlanePoly) (pair : curvePair f g)
    (none : ¬∃ Q, separates f g Q) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra ℂ E) (_ : IsAlgClosed E) (y : LiftCoord → E),
      (∀ i, aeval y (edgeList i)=0) ∧ (∀ j, aeval y (curveList f g j)=0) ∧
      AlgebraicIndependent ℂ (fun s : Competition.Slot => y (.inl (s,0))) := by
  apply Competition.GenericCurvePoint.closed_generic_grid_of_dense f g ((pair_equiv _ _).mp pair)
  intro p hp Q hQ
  by_contra bad
  exact none ⟨Q,(fun u hu h => hQ _ ⟨hu,(position_equiv u).mp h⟩),
    (fun s j => p (s,j)),hp,bad⟩

end PlanarUnitDistances.GridLocus
