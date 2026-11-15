import PlanarUnitDistances.UniformPhysical
import PlanarUnitDistances.RareMassBound

namespace PlanarUnitDistances.UniformPhysical
open Finset Real OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open FiniteLaw FiniteStarCoupling PhysicalLevels IncidenceLabels BoundedHeight
open scoped Classical
noncomputable section

private lemma event_lower {X : Type*} [Fintype X] (U μ : Law X) {a : ℝ} (h : ∀x,a*U.val x≤μ.val x)
    (F : X → Prop) : a*event U F≤event μ F := by
  unfold event avg
  rw [mul_sum]
  apply sum_le_sum
  intro x _; by_cases hf : F x <;> simp [hf,h x]

/-- The rectangle law needed for rare moments is obtained from the same
incidence-density estimates as the bounded-height and common-score arguments. -/
def incidence_rectangles (P Q : Finset Plane) (hP : 0<(P.card:ℝ)) (hQ : 0<(Q.card:ℝ)) (he : 0 < incidences P Q)
    {ξ : ℝ} (hp : ∀p∈P,(27/50:ℝ)/P.card ≤ degree Q p/incidences P Q)
    (hq : ∀q∈Q,(27/50:ℝ)/Q.card ≤ degree P q/incidences P Q)
    (cut : ∀A⊆P,∀B⊆Q,let z := (A.card:ℝ)/P.card*((B.card:ℝ)/Q.card)
      incidences A B/incidences P Q ≤ sqrt z*(z^(1/25:ℝ)+ξ)) :
    RectangleLaw (edgeLaw (unitRows P Q) (incidences P Q) he (unitRows_total P Q)) ξ := by
  letI : Nonempty P := (card_pos.mp (Nat.cast_pos.mp hP)).coe_sort
  letI : Nonempty Q := (card_pos.mp (Nat.cast_pos.mp hQ)).coe_sort
  let law :=  edgeLaw (unitRows P Q) (incidences P Q) he (unitRows_total P Q)
  refine ⟨uniform P,uniform Q,?_,?_,?_⟩
  · intro F G
    have mP : event (uniform P) F=((subsetOf P F).card:ℝ)/P.card := by
      rw [←labelEvent_eq]; simpa only [uniform,Fintype.card_coe] using countEvent P F
    have mQ : event (uniform Q) G=((subsetOf Q G).card:ℝ)/Q.card := by
      rw [←labelEvent_eq]; simpa only [uniform,Fintype.card_coe] using countEvent Q G
    rw [←labelEvent_eq,mP,mQ]
    change labelEvent (fun pq : P×Q => UniformNormalization.weight (unitRows P Q) (incidences P Q) pq.1 pq.2) _≤_
    rw [incidenceEvent]
    let z := ((subsetOf P F).card:ℝ)/P.card*(((subsetOf Q G).card:ℝ)/Q.card)
    have hz : 0≤z := by dsimp only [z]; positivity
    have hh : (sqrt z)^(2/25:ℝ)=z^(1/25:ℝ) := by
      rw [sqrt_eq_rpow,←rpow_mul hz]; norm_num
    exact (cut _ (subsetOf_subset P F) _ (subsetOf_subset Q G)).trans_eq (by rw [←hh])
  · intro F
    have hlt (p : P) : 27/50*(uniform P).val p≤(left law).val p := by
      rw [edge_left,unitRows_point_degree]
      simpa only [uniform,Fintype.card_coe,div_eq_mul_inv] using hp p p.prop
    apply (event_lower (uniform P) (left law) hlt F).trans_eq
    unfold event left; rw [push_avg]
  · intro G
    have hlt (q : Q) : 27/50*(uniform Q).val q≤(right law).val q := by
      rw [edge_right,centerLaw,unitRows_center_degree]
      simpa only [uniform,Fintype.card_coe,div_eq_mul_inv] using hq q q.prop
    apply (event_lower (uniform Q) (right law) hlt G).trans_eq
    unfold event right; rw [push_avg]

end
end PlanarUnitDistances.UniformPhysical
