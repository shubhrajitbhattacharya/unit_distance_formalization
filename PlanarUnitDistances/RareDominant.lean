import PlanarUnitDistances.Matching
import PlanarUnitDistances.RareIntegral

namespace OAI.PlanarUnitDistances.PhysicalLevels
open Finset FiniteLaw FiniteStarCoupling CommonTemplate RareScore CrossStructure MeasureTheory
open _root_.PlanarUnitDistances _root_.PlanarUnitDistances.ComparisonConstants
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

structure RectangleLaw (π : Law (P×Q)) (ξ : ℝ) where
  U : Law P
  V : Law Q
  rect : ∀ (A : P → Prop) (B : Q → Prop),event π (fun pq => A pq.1 ∧ B pq.2) ≤
    let b := Real.sqrt (event U A*event V B)
    b*(b^(2/25:ℝ)+ξ)
  lowP : ∀A : P → Prop,(27/50:ℝ)*event U A≤event π (fun pq => A pq.1)
  lowQ : ∀B : Q → Prop,(27/50:ℝ)*event V B≤event π (fun pq => B pq.2)

lemma labelEvent_eq {X : Type*} [Fintype X] (μ : Law X) (A : X → Prop) :
    labelEvent μ.val A=event μ A := by
  unfold labelEvent event avg
  apply sum_congr rfl; intro x _; by_cases h : A x <;> simp [h]

theorem dominant {A : Type*} [Fintype A] [Nonempty A] (π : Law (P×Q)) {ξ : ℝ}
    (E : RectangleLaw π ξ) (hξ : 0≤ξ) (hs : ξ≤1/(2:ℝ)^100) (x : P → A) (y : Q → A)
    (h : event π (fun pq => x pq.1≠y pq.2)≤1/(2:ℝ)^52) : ∃u,
    event π (fun pq => x pq.1≠u)+event π (fun pq => y pq.2≠u) ≤ 2*event π (fun pq => x pq.1≠y pq.2) := by
  let u := push E.U x
  let v := push E.V y
  have cu (a : A) : event E.U (fun p => x p≠a)=1-u.val a := event_compl E.U _
  have cv (a : A) : event E.V (fun q => y q≠a)=1-v.val a := event_compl E.V _
  have match' := matching_for_edge_law π.val (fun z => x z.1) (fun z => y z.2) u.val v.val ξ
    π.nonneg π.total u.nonneg v.nonneg u.total v.total hξ hs
    (fun a => (labelEvent_eq π _).trans_le (E.rect (fun p => x p=a) (fun q => y q=a)))
    (fun a => by rw [labelEvent_eq,←cu,←cv]; exact E.rect (fun p => x p≠a) (fun q => y q≠a))
    (fun a => by rw [labelEvent_eq,←cu]; exact E.lowP _)
    (fun a => by rw [labelEvent_eq,←cv]; exact E.lowQ _)
  simpa only [labelEvent_eq] using match'.1 ((labelEvent_eq π _).trans_le h)

def rareBit (π : Law (P×Q)) (t : Record P Q) :=
  decide (event π (fun e => t.bit e.1 e.2=true)≤1/2)

lemma minority_probability (π : Law (P×Q)) (t : Record P Q) :
    event π (fun e => t.bit e.1 e.2=rareBit π t)=minority π t := by
  let f := event π (fun e => t.bit e.1 e.2=true)
  have zero : event π (fun e => t.bit e.1 e.2=false)=1-f := by
    rw [←event_compl]
    exact event_congr _ (fun e => by cases t.bit e.1 e.2 <;> simp)
  by_cases h : f≤1/2
  · have rb : rareBit π t=true := decide_eq_true h
    rw [rb]
    exact (min_eq_left (show f≤1-f by linarith)).symm
  · have rb : rareBit π t=false := decide_eq_false h
    rw [rb,zero]
    exact (min_eq_right (show 1-f≤f by linarith)).symm

def shared {A : Type*} (r : Bool) (x : A×A) := if r then x.2 else x.1

theorem mismatch (π : Law (P×Q)) (t : Record P Q) :
    event π (fun e => shared (rareBit π t) (t.x e.1)≠shared (rareBit π t) (t.y e.2)) ≤
      minority π t+inconsistency π t.bit t.x t.y := by
  rw [←minority_probability]
  apply le_trans _ (event_union_le π (fun e => t.bit e.1 e.2=rareBit π t)
    (fun e => ¬Consistent (t.bit e.1 e.2) (t.x e.1) (t.y e.2)))
  apply event_mono; intro e he
  cases r : rareBit π t <;> cases b : t.bit e.1 e.2 <;> simp_all [shared,Consistent]

/-- Point and center exceptional mass together cost at most 2(f+m). This
selects one function on the finite record space, measurable automatically. -/
theorem choose_dominant (π : Law (P×Q)) {ξ : ℝ} (E : RectangleLaw π ξ)
    (hξ : 0≤ξ) (hs : ξ≤1/(2:ℝ)^100) : ∃l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q),
    ∀t∈goodRare π, pointException π (rareBit π t) (l t) t.x+centerException π (rareBit π t) (l t) t.y ≤
      2*(minority π t+inconsistency π t.bit t.x t.y) := by
  have pick (t : Record P Q) : ∃c : Finset (P⊕Q), t∈goodRare π →
      pointException π (rareBit π t) (c,c) t.x+centerException π (rareBit π t) (c,c) t.y ≤
      2*(minority π t+inconsistency π t.bit t.x t.y) := by
    by_cases h : t∈goodRare π
    · have he : 2*dy 1800≤1/(2:ℝ)^52 := by
        have h1 := antitone (by decide : 53≤1800)
        have h2 : 2*dy 53=1/(2:ℝ)^52 := by norm_num [dy]
        exact (mul_le_mul_of_nonneg_left h1 (by norm_num)).trans_eq h2
      have hmi : minority π t<dy 1800 := lt_of_not_ge h.1
      have hbad : inconsistency π t.bit t.x t.y≤dy 1800 := h.2
      have bound := (mismatch π t).trans ((add_le_add hmi.le hbad).trans
        ((two_mul (dy 1800)).symm.trans_le he))
      obtain ⟨c,hc⟩ := dominant π E hξ hs (fun p => shared (rareBit π t) (t.x p))
        (fun q => shared (rareBit π t) (t.y q)) bound
      refine ⟨c,fun _ => ?_⟩
      have imp := hc.trans (mul_le_mul_of_nonneg_left (mismatch π t) (by norm_num))
      cases hr : rareBit π t <;> simpa only [hr,pointException,centerException,exceptional,shared,
        Bool.false_eq_true,ite_false,ite_true] using imp
    · exact ⟨∅,fun h' => (h h').elim⟩
  choose c hc using pick
  exact ⟨fun t => (c t,c t),hc⟩

end
end OAI.PlanarUnitDistances.PhysicalLevels
