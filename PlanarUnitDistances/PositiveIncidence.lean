import PlanarUnitDistances.PositiveAtoms
import PlanarUnitDistances.UniformIncidenceLaw
import PlanarUnitDistances.GeometricHeightLaw
import PlanarUnitDistances.CommonCoordinates

namespace PlanarUnitDistances.UniformPhysical
open Finset OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open CommonFieldModel FiniteLaw FiniteStarCoupling TemplateCoupling
open scoped Classical
noncomputable section
variable {P Q : Finset CommonFieldModel.Plane}

abbrev unitEdgeLaw (he : 0 < incidences P Q) := edgeLaw (unitRows P Q) (incidences P Q) he (unitRows_total P Q)

private theorem unitRow_of_positive (he : 0 < incidences P Q) (p : P) (q : Q)
    (h : 0<(unitEdgeLaw he).val (p,q)) : p∈unitRows P Q q := by
  by_contra hn
  change 0<UniformNormalization.weight (unitRows P Q) (incidences P Q) p q at h
  simp [UniformNormalization.weight,hn] at h

theorem positive_row_incidence (he : 0 < incidences P Q) (p : P)
    (hp : 0<(left (unitEdgeLaw he)).val p) (q : PositiveAtom (row (unitEdgeLaw he) p)) : p∈unitRows P Q q.val := by
  exact unitRow_of_positive he p q.val ((row_weight (unitEdgeLaw he) p q.val) ▸ mul_pos hp q.prop)

theorem positive_col_incidence (he : 0 < incidences P Q) (q : Q)
    (hq : 0<(right (unitEdgeLaw he)).val q) (p : PositiveAtom (col (unitEdgeLaw he) q)) : p.val∈unitRows P Q q := by
  exact unitRow_of_positive he p.val q ((col_weight (unitEdgeLaw he) p.val q) ▸ mul_pos hq p.prop)

theorem positive_slice_incidence {T : Type} [Fintype T] (he : 0 < incidences P Q)
    (a : Q→Law T) (j : T) (p : P)
    (base : 0<(templates (unitEdgeLaw he) a).val j*(left (slice (unitEdgeLaw he) a j)).val p)
    (q : PositiveAtom (row (slice (unitEdgeLaw he) a j) p)) : p∈unitRows P Q q.val := by
  let G := unitEdgeLaw he
  have eq := slice_weight G a j (p,q.val)
  rw [←row_weight (slice G a j) p q.val,←mul_assoc] at eq
  have positive : 0<G.val (p,q.val)*(a q.val).val j := eq ▸ mul_pos base q.prop
  apply unitRow_of_positive he
  by_contra hn
  have hz : G.val (p,q.val)=0 := le_antisymm (le_of_not_gt hn) (G.nonneg _)
  rw [hz,zero_mul] at positive
  exact (lt_irrefl _ positive)

/-- Reversing both field differences leaves the original unit equation
unchanged for a point-based posterior over its incident centers. -/
theorem reverse_unit (M : Model P Q) {p : P} {q : Q} (h : p∈unitRows P Q q) :
    (M.z (.inr q)-M.z (.inl p))*(M.w (.inr q)-M.w (.inl p))=1 := by
  rw [←neg_sub (M.z (.inl p)) (M.z (.inr q)),←neg_sub (M.w (.inl p)) (M.w (.inr q)),neg_mul_neg]
  exact M.unit_identity p q (mem_filter.mp h).2

end
end PlanarUnitDistances.UniformPhysical

