import PlanarUnitDistances.FullHistoryLists
import PlanarUnitDistances.TemplateDiagonal
import PlanarUnitDistances.UniformIncidenceLaw

namespace PlanarUnitDistances.ComparisonConstants
open Real Filter Finset OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open FiniteLaw FiniteStarCoupling TemplateCoupling UniformPhysical
open scoped Topology Classical
noncomputable section

/-- For the actual uniform edge law every supported posterior point row
has mass 1/d(p) at each neighbor and zero elsewhere. -/
theorem posterior_row_cap {P Q : Finset Plane} (he : 0 < incidences P Q) (p : P)
    (hp : 0<degree Q p) (q : Q) :
    let G := edgeLaw (unitRows P Q) (incidences P Q) he (unitRows_total P Q)
    (row G p).val q≤(degree Q p)⁻¹ := by
  let G := edgeLaw (unitRows P Q) (incidences P Q) he (unitRows_total P Q)
  have e : (left G).val p=degree Q p/incidences P Q := by rw [edge_left,unitRows_point_degree]
  have pos : 0<(left G).val p := e.symm ▸ div_pos hp he
  change (row G p).val q≤(degree Q p)⁻¹
  rw [row_val G pos q,e]
  change UniformNormalization.weight (unitRows P Q) (incidences P Q) p q / _≤_
  unfold UniformNormalization.weight
  by_cases mem : p∈unitRows P Q q
  · rw [ite_eq_left mem]
    apply le_of_eq
    field_simp
  · rw [ite_eq_right mem,zero_div]
    exact (inv_pos.mpr hp).le


end
end PlanarUnitDistances.ComparisonConstants

