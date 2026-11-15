import PlanarUnitDistances.ListComparisons
import PlanarUnitDistances.UniformNormalization

namespace PlanarUnitDistances.UniformPhysical
open Finset OAI.PlanarUnitDistances FiniteLaw FiniteStarCoupling
open UniformNormalization BoundedHeight
open scoped Classical
noncomputable section
variable {P Q : Type} [Fintype P] [Fintype Q]

/-- Uniform atomic law of the actual incidences. The denominator is the given
positive number of recorded edges, including all and only the allowed pairs. -/
def edgeLaw (S : Q → Finset P) (e : ℝ) (he : 0<e) (ht : ∑q,((S q).card:ℝ)=e) : Law (P×Q) where
  val pq := weight S e pq.1 pq.2
  nonneg _ := by unfold weight; split <;> positivity
  total := by
    rw [Fintype.sum_prod_type,Finset.sum_comm]; simp only [weight_right,centerLaw,←sum_div,ht,div_self he.ne']

theorem edge_left (S : Q → Finset P) (e : ℝ) (he : 0<e) (ht : ∑q,((S q).card:ℝ)=e) (p : P) :
    (FiniteStarCoupling.left (edgeLaw S e he ht)).val p=((pointCenters S p).card:ℝ)/e := by
  rw [left_val]; exact weight_left S e p
theorem edge_right (S : Q → Finset P) (e : ℝ) (he : 0<e) (ht : ∑q,((S q).card:ℝ)=e) (q : Q) :
    (right (edgeLaw S e he ht)).val q=centerLaw S e q := by
  rw [right_val]; exact weight_right S e q

end
end PlanarUnitDistances.UniformPhysical
