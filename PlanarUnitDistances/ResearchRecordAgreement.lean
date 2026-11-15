import PlanarUnitDistances.ResearchCellIdentification
import PlanarUnitDistances.ResearchCommonDisagreement
import PlanarUnitDistances.ResearchThresholds
import PlanarUnitDistances.RareDominant

namespace PlanarUnitDistances.ResearchPhysical
open OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence CommonFieldModel
open Competition.IncidencePiece PhysicalLevels CommonTemplate CrossStructure FiniteLaw
open Finset NumberField UniformNormalization FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q : Finset Competition.Plane}

def tagState (t : Record P Q) : P⊕Q→Finset (P⊕Q)×Finset (P⊕Q) := Sum.elim t.x t.y

structure RecordAgreement (M : Model P Q) (b : CoordinateLevel (toPiece M).Label) (t : Record P Q) : Prop where
  bits : ∀(p : P) (q : Q),dist p.val q.val=1 → b.bit (p.val,q.val)=t.bit p q
  majority : b.majority=decide (1/2<(toPiece M).edgeProb (fun e => b.bit e=true))
  classes : ∀x y : P⊕Q,
    ((b.label (planeVertex x)).1=(b.label (planeVertex y)).1 ↔ (tagState t x).1=(tagState t y).1) ∧
    ((b.label (planeVertex x)).2=(b.label (planeVertex y)).2 ↔ (tagState t x).2=(tagState t y).2)

theorem arch_agreement (M : Model P Q) (v : InfinitePlace M.field) (U V : ℝ×ℝ) (s : ℝ) :
    RecordAgreement M ((toPiece M).archRecord v U V s) (arch v U V M.z M.w s) := by
  refine ⟨?_,rfl,?_⟩
  · intro p q h
    rw [arch_bit _ _ _ _ _ _ (full M p p.prop q q.prop h)]
    change decide (s < -Real.log (v ((toPiece M).Z p-(toPiece M).Z q)))=_
    rw [z_point,z_center]; rfl
  · intro x y
    have eq (a : P⊕Q) : tagState (arch v U V M.z M.w s) a=PhysicalLabels.archPair v U V M.z M.w s a := by
      cases a <;> rfl
    rw [eq,eq]; exact arch_coordinate_classes M v U V s x y

theorem finite_agreement (M : Model P Q) (v : FinitePlace M.field) (s : ℝ) :
    RecordAgreement M ((toPiece M).finiteRecord v s) (PhysicalLevels.finite v M.z M.w s) := by
  refine ⟨?_,rfl,?_⟩
  · intro p q h
    rw [finite_edge_bit _ _ _ _ (full M p p.prop q q.prop h)]
    change decide (s < -Real.log (v ((toPiece M).Z p-(toPiece M).Z q)))=_
    rw [z_point,z_center]; rfl
  · intro x y
    have eq (a : P⊕Q) : tagState (PhysicalLevels.finite v M.z M.w s) a=PhysicalLabels.finitePair v M.z M.w s a := by
      cases a <;> rfl
    rw [eq,eq]; exact finite_coordinate_classes M v s x y

theorem physical_event (M : Model P Q) (he : 0 < incidences P Q)
    (A : Competition.Plane×Competition.Plane→Prop) (B : P×Q→Prop)
    (agree : ∀(p : P) (q : Q),dist p.val q.val=1 → (A (p.val,q.val) ↔ B (p,q))) :
    (toPiece M).edgeProb A=event (incidenceLaw P Q he) B := by
  rw [edgeProb_eq_sum]
  unfold event avg
  apply sum_congr rfl
  rintro ⟨p,q⟩ _
  change _=weight (unitRows P Q) (incidences P Q) p q * _
  have mem : p∈unitRows P Q q ↔ dist p.val q.val=1 := by simp [unitRows,unitNeighbors]
  by_cases h : dist p.val q.val=1
  · by_cases a : A (p.val,q.val) <;> simp_all [weight,agree p q h]
  · simp [h,weight,mem]

theorem RecordAgreement.rare_bit {M : Model P Q} {b : CoordinateLevel (toPiece M).Label} {t : Record P Q}
    (H : RecordAgreement M b t) (he : 0 < incidences P Q) : b.majority= !(rareBit (incidenceLaw P Q he) t) := by
  let π := incidenceLaw P Q he
  have eq := physical_event M he (fun e => b.bit e=true) (fun pq => t.bit pq.1 pq.2=true)
    (fun p q h => by rw [H.bits p q h])
  rw [H.majority,eq]
  unfold rareBit
  change decide (1/2<event π (fun pq => t.bit pq.1 pq.2=true)) = !decide (event π (fun pq => t.bit pq.1 pq.2=true)≤1/2)
  by_cases h : event π (fun pq => t.bit pq.1 pq.2=true)≤1/2
  · simp only [h,not_lt_of_ge h,decide_false,decide_true,Bool.not_true]
  · simp only [h,lt_of_not_ge h,decide_false,decide_true,Bool.not_false]

theorem RecordAgreement.rare_masses {M : Model P Q} {b : CoordinateLevel (toPiece M).Label} {t : Record P Q}
    (H : RecordAgreement M b t) (he : 0 < incidences P Q) :
    (toPiece M).minorityMass b=minority (incidenceLaw P Q he) t ∧
    (toPiece M).inconsistentMass b=inconsistency (incidenceLaw P Q he) t.bit t.x t.y := by
  let π := incidenceLaw P Q he
  constructor
  · rw [←minority_probability]
    apply physical_event M he
    intro p q h
    rw [H.bits p q h,H.rare_bit he]
    cases t.bit p q <;> cases rareBit (incidenceLaw P Q he) t <;> decide
  · apply physical_event M he
    intro p q h
    apply not_congr
    obtain ⟨z,w⟩ := H.classes (.inl p) (.inr q)
    change ((b.label p.val).1=(b.label q.val).1 ↔ (t.x p).1=(t.y q).1) at z
    change ((b.label p.val).2=(b.label q.val).2 ↔ (t.x p).2=(t.y q).2) at w
    unfold CoordinateLevel.consistent Consistent
    rw [H.bits p q h]
    cases t.bit p q <;> simp [z,w,and_comm]

end
end PlanarUnitDistances.ResearchPhysical
