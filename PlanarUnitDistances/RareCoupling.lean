import PlanarUnitDistances.ListComparisons
import PlanarUnitDistances.RareSlots

namespace OAI.PlanarUnitDistances.RareScore
open Finset FiniteLaw FiniteStarCoupling TemplateCoupling CrossStructure
open scoped Classical
noncomputable section
variable {P Q A B Θ : Type*} [Fintype P] [Fintype Q] [Fintype Θ]
def pointScore (π : Law (P×Q)) (r : Bool) (l : A×B) (x : P → A×B)
    (y : Q → A×B) (bit : P → Q → Bool) :=
  avg (left π) (fun p => avg (pair (row π p) (row π p)) (fun qq =>
    slot r l (x p) (y qq.1) (y qq.2) (bit p qq.1) (bit p qq.2)))
def centerScore (π : Law (P×Q)) (r : Bool) (l : A×B) (x : P → A×B)
    (y : Q → A×B) (bit : P → Q → Bool) :=
  avg (right π) (fun q => avg (pair (col π q) (col π q)) (fun pp =>
    slot r l (y q) (x pp.1) (x pp.2) (bit pp.1 q) (bit pp.2 q)))
def pointException (π : Law (P×Q)) (r : Bool) (l : A×B) (x : P → A×B) :=
  event π (fun pq => exceptional r l (x pq.1))
def centerException (π : Law (P×Q)) (r : Bool) (l : A×B) (y : Q → A×B) :=
  event π (fun pq => exceptional r l (y pq.2))
def jointException (π : Law (P×Q)) (r : Bool) (l : A×B) (x : P → A×B) (y : Q → A×B) :=
  event π (fun pq => exceptional r l (x pq.1) ∧ exceptional r l (y pq.2))
def edgeError (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B) :=
  event π (fun pq => ¬Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))

theorem point_lower (π : Law (P×Q)) (r : Bool) (l : A×B) (x : P → A×B) (y : Q → A×B)
    (bit : P → Q → Bool) :
    2*(pointException π r l x-centerException π r l y)-4*jointException π r l x y-
      6*edgeError π bit x y ≤ pointScore π r l x y bit := by
  have h := avg_mono (left π) (fun p => star_lower (row π p) r l (x p) y (bit p))
  simp only [avg_sub,avg_smul,row_event] at h
  have hP : avg (left π) (fun p => ind (exceptional r l (x p)))=pointException π r l x := by
    rw [left,push_avg]; rfl
  rw [hP] at h
  change 2*_ - 4*jointException π r l x y-2*centerException π r l y-6*edgeError π bit x y ≤ _ at h
  unfold pointScore
  linarith only [h]

theorem center_lower (π : Law (P×Q)) (r : Bool) (l : A×B) (x : P → A×B) (y : Q → A×B)
    (bit : P → Q → Bool) :
    2*(centerException π r l y-pointException π r l x)-4*jointException π r l x y-
      6*edgeError π bit x y ≤ centerScore π r l x y bit := by
  have h := avg_mono (right π) (fun q => star_lower (col π q) r l (y q) x (fun p => bit p q))
  simp only [avg_sub,avg_smul,col_event] at h
  have hQ : avg (right π) (fun q => ind (exceptional r l (y q)))=centerException π r l y := by
    rw [right,push_avg]; rfl
  have hj : event π (fun pq => exceptional r l (y pq.2) ∧ exceptional r l (x pq.1)) =
      jointException π r l x y := event_congr _ (fun _ => and_comm)
  have he : event π (fun pq => ¬Consistent (bit pq.1 pq.2) (y pq.2) (x pq.1)) = edgeError π bit x y := by
    apply event_congr
    intro pq
    cases hh : bit pq.1 pq.2 <;> simp only [Consistent,Bool.false_eq_true,ite_false,ite_true] <;> aesop
  rw [hj,he,hQ] at h
  change 2*_ - 4*jointException π r l x y-2*pointException π r l x-6*edgeError π bit x y ≤ _ at h
  unfold centerScore
  linarith only [h]

/-- Although the second center in the T experiment depends on the sampled list,
each tested edge still has exactly the original marginal. -/
theorem list_lower (π : Law (P×Q)) (a : Q → Law Θ) (r : Bool) (l : A×B)
    (x : P → A×B) (y : Q → A×B) (bit : P → Q → Bool) :
    2*(pointException π r l x-centerException π r l y)-4*jointException π r l x y-
      6*edgeError π bit x y ≤ avg (templates π a) (fun θ => pointScore (slice π a θ) r l x y bit) := by
  have h := avg_mono (templates π a) (fun θ => point_lower (slice π a θ) r l x y bit)
  have invariant (g : P×Q → Prop) : avg (templates π a) (fun θ => event (slice π a θ) g)=event π g := by
    rw [slice_event]
    unfold event
    apply avg_congr
    intro pq
    by_cases hg : g pq <;> simp [hg,avg_const]
  simpa only [avg_sub,avg_smul,pointException,centerException,jointException,edgeError,invariant] using h

end
end OAI.PlanarUnitDistances.RareScore
