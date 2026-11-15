import PlanarUnitDistances.ConstructiblePositions
import PlanarUnitDistances.SimultaneousCurveNonvanishing
import PlanarUnitDistances.UniformChartSeparation
import PlanarUnitDistances.UniformGridLocus
import PlanarUnitDistances.GridProperness

namespace PlanarUnitDistances.GridLocus
open MvPolynomial

/-- The compatibility locus has a separating equation of uniformly bounded
degree on every eligible curve product. Its bound is chosen once from the
finite family of charts for the fixed 8-by-4 tangent system. -/
theorem uniform_separating_degree :
    ∃ E : ℕ, ∀ f g, curvePair f g → ∃ F : TuplePoly, F.totalDegree ≤ E ∧ separates f g F := by
  let S : Set Competition.GridTuple := {x | Competition.PositionSystem x}
  obtain ⟨T,description⟩ := Competition.GridElimination.position_charts
  obtain ⟨E,uniform⟩ := UniformSeparation.uniform_separator (S:=S) T description
  refine ⟨E,?_⟩
  intro f g pair
  let W := Competition.curveProduct f g
  have product (F G : TuplePoly) : UniformSeparation.NonzeroOn W F →
      UniformSeparation.NonzeroOn W G → UniformSeparation.NonzeroOn W (F*G) :=
    Competition.GenericCurvePoint.nonzero_product_on_curves ((pair_equiv f g).mp pair)
  obtain ⟨Q,hvan,u,hu,hQ⟩ := proper_grid_locus f g pair
  have initial : ∃ H : TuplePoly, UniformSeparation.NonzeroOn W H ∧
      ∀ x ∈ W, x∈S → eval x H=0 := by
    refine ⟨Q,⟨fun e => u e.1 e.2,hu,hQ⟩,?_⟩
    intro x hx hS
    exact hvan (fun s d => x (s,d)) hx ((position_equiv _).mpr hS)
  obtain ⟨F,deg,van,x,hx,nonzero⟩ := uniform W product initial
  refine ⟨F,deg,?_,fun s d => x (s,d),hx,nonzero⟩
  intro v hv h
  exact van (fun e => v e.1 e.2) hv ((position_equiv v).mp h)

/-- The original uniform-degree predicate, including its original
nonvanishing witness and every compatible tuple of the original product. -/
theorem uniform_exceptional_degree : UniformExceptionalDegree := by
  obtain ⟨E,h⟩ := uniform_separating_degree
  exact ⟨E,fun f g pair _ _ => h f g pair⟩

end PlanarUnitDistances.GridLocus
