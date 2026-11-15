import PlanarUnitDistances.UniformNormalization
import PlanarUnitDistances.WalkBudget

namespace PlanarUnitDistances
open OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open Finset Real BoundedHeight UniformNormalization OAI.PlanarUnitDistances.LocalHeightTransfer
open scoped Classical
noncomputable section

def unitRows (P Q : Finset Plane) (q : Q) : Finset P := unitNeighbors P q

theorem unitRows_center_degree (P Q : Finset Plane) (q : Q) :
    ((unitRows P Q q).card:ℝ) = degree P q := unitNeighbors_card P q

theorem unitRows_point_degree (P Q : Finset Plane) (p : P) :
    ((pointCenters (unitRows P Q) p).card:ℝ) = degree Q p := by
  rw [← unitNeighbors_card Q p]
  congr 2
  ext q
  simp [pointCenters,unitRows,unitNeighbors,dist_comm (p:Plane)]

theorem unitRows_total (P Q : Finset Plane) :
    (∑ q, ((unitRows P Q q).card:ℝ)) = incidences P Q := by
  simp only [unitRows_center_degree,incidences]
  exact Finset.sum_attach Q _

theorem unitRows_information (P Q : Finset Plane) (hq : ∀ q ∈ Q, 0 < degree P q) :
    unitWalkInformation P Q = twoEdgeInformation (unitRows P Q) (incidences P Q) := by
  have nonemp (q : Q) : (unitRows P Q q).Nonempty := card_pos.mp (Nat.cast_pos.mp
    ((unitRows_center_degree P Q q).symm ▸ hq q q.2))
  have κ : unitCenterLaw P Q = centerLaw (unitRows P Q) (incidences P Q) := by
    funext q; simp only [unitCenterLaw, centerLaw, unitRows_center_degree]
  have w : (fun q : Q => unitNeighborLaw P q) = neighborLaw (unitRows P Q) := by
    funext q p
    rw [neighborLaw, if_pos (nonemp q), unitRows_center_degree]
    by_cases hp : p ∈ unitNeighbors P q <;> simp [unitNeighborLaw,unitRows,hp]
  simp only [unitWalkInformation,twoEdgeInformation,κ,w]

namespace IncidenceLabels

def subsetOf (P : Finset Plane) (F : P → Prop) :=
  (univ.filter F).map (Function.Embedding.subtype (·∈P))

theorem subsetOf_subset (P : Finset Plane) (F : P → Prop) : subsetOf P F ⊆ P := by
  intro x hx
  obtain ⟨p,_,rfl⟩ := Finset.mem_map.mp hx
  exact p.2

theorem countEvent (P : Finset Plane) (F : P → Prop) :
    labelEvent (fun _ : P => (P.card : ℝ)⁻¹) F = ((subsetOf P F).card:ℝ)/P.card := by
  simp only [labelEvent,subsetOf,card_map,← Finset.sum_filter, Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv]

theorem incidenceEvent (P Q : Finset Plane) (F : P → Prop) (G : Q → Prop) :
    labelEvent (fun x : P×Q => weight (unitRows P Q) (incidences P Q) x.1 x.2)
      (fun x => F x.1 ∧ G x.2) = incidences (subsetOf P F) (subsetOf Q G)/incidences P Q := by
  let e := incidences P Q
  have term (q : Q) (p : P) :
      (@ite ℝ (F p ∧ G q) (Classical.propDecidable _) (weight (unitRows P Q) e p q) 0) =
      (if G q then (if F p then (if dist (p:Plane) (q:Plane)=1 then (1:ℝ) else 0) else 0) else 0)/e := by
    by_cases hf : F p <;> by_cases hg : G q <;> by_cases hd : dist (p:Plane) (q:Plane) = 1 <;>
      simp [hf,hg,hd,weight,unitRows,unitNeighbors,one_div]
  unfold labelEvent
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  change (∑ q : Q, ∑ p : P, @ite ℝ (F p ∧ G q) (Classical.propDecidable _) (weight (unitRows P Q) e p q) 0) = _
  simp only [term,← Finset.sum_div]
  congr 1
  unfold incidences
  simp_rw [degree_sum]
  simp only [subsetOf, Finset.sum_map, Finset.sum_filter, Function.Embedding.subtype_apply]
  apply sum_congr rfl
  intro q _
  by_cases hg : G q
  · simp only [hg,if_true]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hf : F p <;> by_cases hd : dist (p:Plane) (q:Plane)=1 <;> simp [hf,hd]
  · simp [hg]

end IncidenceLabels
open IncidenceLabels

/-- The rectangle expansion and lower marginal inequalities from the actual
Euclidean graph imply the label-control hypothesis for its arithmetic normalization. -/
theorem unitRows_label_control (P Q : Finset Plane) (hP : 0 < (P.card:ℝ)) (hQ : 0 < (Q.card:ℝ))
    (he : 0 < incidences P Q) {ξ : ℝ} (hξ : 0 ≤ ξ) (hξs : ξ ≤ 1/(2:ℝ)^100)
    (hp : ∀ p ∈ P, (27/50:ℝ)/P.card ≤ degree Q p/incidences P Q)
    (hq : ∀ q ∈ Q, (27/50:ℝ)/Q.card ≤ degree P q/incidences P Q)
    (hcut : ∀ A ⊆ P, ∀ B ⊆ Q, let z := (A.card:ℝ)/P.card*((B.card:ℝ)/Q.card)
      incidences A B/incidences P Q ≤ sqrt z*(z^(1/25:ℝ)+ξ)) :
    LabelControl 28 (weight (unitRows P Q) (incidences P Q)) := by
  let w := weight (unitRows P Q) (incidences P Q)
  have mw (p : P) : (∑ q, w p q) = degree Q p/incidences P Q := by
    change left (weight _ _) p = _
    rw [weight_left,unitRows_point_degree]
  have nw (q : Q) : (∑ p, w p q) = degree P q/incidences P Q := by
    rw [show (∑ p, w p q) = centerLaw (unitRows P Q) (incidences P Q) q from weight_right _ _ q]
    rw [centerLaw,unitRows_center_degree]
  have mass : ∑ p, ∑ q, w p q = 1 := by
    rw [sum_comm]
    simp only [nw,← sum_div, ← unitRows_center_degree P Q,unitRows_total,div_self he.ne']
  apply HeightTransfer.label_control_of_rectangles w (fun _ => (P.card:ℝ)⁻¹) (fun _ => (Q.card:ℝ)⁻¹)
    (fun p q => by dsimp [w,weight]; split_ifs <;> positivity) mass (fun _ => by positivity)
    (fun _ => by positivity) (by simp [hP.ne']) (by simp [hQ.ne']) hξ hξs
  · intro F G
    rw [incidenceEvent, countEvent,countEvent]
    let z := ((subsetOf P F).card:ℝ)/P.card*(((subsetOf Q G).card:ℝ)/Q.card)
    have hz : 0 ≤ z := by dsimp [z]; positivity
    have eqpow : (sqrt z)^(2/25:ℝ) = z^(1/25:ℝ) := by
      rw [sqrt_eq_rpow, ← rpow_mul hz]
      norm_num
    exact (hcut _ (subsetOf_subset P F) _ (subsetOf_subset Q G)).trans_eq (by rw [← eqpow])
  · intro F
    unfold labelEvent
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply sum_le_sum
    intro p _
    by_cases hf : F p
    · simp only [hf,if_true,mw]
      simpa only [div_eq_mul_inv] using hp p p.2
    · simp [hf]
  · intro G
    unfold labelEvent
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
    apply sum_le_sum
    intro q _
    by_cases hg : G q
    · simp only [hg,if_true,nw]
      simpa only [div_eq_mul_inv] using hq q q.2
    · simp [hg]

end
end PlanarUnitDistances
