import PlanarUnitDistances.FlankSlot
import PlanarUnitDistances.RareSlots

namespace PlanarUnitDistances.Flanks
open Set Real OAI.PlanarUnitDistances
open scoped Classical
noncomputable section
variable {I A B : Type*}

/-- The observed summand in the three experiments. The two entries in a
pair are evaluated under the same base and the same level. -/
def observedSlot (common good : Prop) (r : Bool) (l x : A×B) (g : ℝ)
    (bit : I → Bool) (y : I → A×B) (i j : I) :=
  if common then StarScore.slot g bit y i j
  else if good then RareScore.slot r l x (y i) (y j) (bit i) (bit j)
  else -RareScore.ind (bit i≠bit j)

/-- Direct bound on a coincident pair, retaining the exceptional status of
its base. Integrating yields the weight \(2(W_c+H_x^*)\). -/
theorem diagonal_observedSlot (cc good : Prop) (r : Bool) (l x : A×B) (g : ℝ)
    (bit : I → Bool) (y : I → A×B) (i : I) :
    observedSlot cc good r l x g bit y i i ≤
      2*RareScore.ind cc+2*RareScore.ind (¬cc ∧ good ∧ RareScore.exceptional r l x) := by
  by_cases hc : cc
  · cases hi : bit i <;>
      simpa [observedSlot,hc,StarScore.slot,hi,RareScore.ind] using StarScore.coefficient_upper g
  by_cases hg : good
  · by_cases ex : RareScore.exceptional r l x <;>
      cases hi : bit i <;> cases r <;>
      simp_all [observedSlot,RareScore.slot,RareScore.nonshared,RareScore.ind]
  · simp [observedSlot,hc,hg,RareScore.ind]

/-- The bit-threshold version of Lemma 5's integrand agrees, pointwise on
the physical interval, with the old common/rare record summand. The guard
on the positive rare term uses both the good-level and base-exception
tests. The disagreement is subtracted on all three classes of levels. -/
theorem observedSlot_eq (lo hi ε s : ℝ) (inside : s∈Icc lo hi) (cut : ε≤1/2)
    (f g : ℝ → ℝ) (good : ℝ → Prop) (level : ℝ → A×B) (base : ℝ → A×B)
    (Y : ℝ → I → A×B) (Z : I → ℝ) (i j : I) :
    let r := fun v => decide (f v≤1/2)
    let bits := fun v k => decide (v<Z k)
    let selected := fun v => good v ∧ RareScore.exceptional (r v) (level v) (base v)
    observedSlot (ε ≤ min (f s) (1-f s)) (good s) (r s) (level s) (base s) (g s)
      (bits s) (Y s) i j =
      positive lo hi ε (Z i) (Z j) f g
        (fun v => (Y v i).1=(Y v j).1) (fun v => (Y v i).2=(Y v j).2) selected s-
      RareScore.ind (bits s i≠bits s j) := by
  intro r bits selected
  let ca := ε≤f s ∧ f s≤1-ε
  have hcomm : (ε ≤ min (f s) (1-f s))↔ca := by
    rw [le_min_iff]; dsimp only [ca]; constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  have span : s∈commonRegion lo hi ε f ↔ ca := ⟨fun h => h.2,fun h => ⟨inside,h⟩⟩
  have opposite (a : ℝ) : a ≤ s ↔ ¬s<a := not_lt.symm
  by_cases inC : ca
  · have low : ¬f s<ε := not_lt.mpr inC.1
    have high : ¬1-ε<f s := not_lt.mpr inC.2
    rw [observedSlot,if_pos (hcomm.mpr inC)]
    simp only [positive,rarePositive,commonPositive,span,inC,low,high,true_and,false_and,and_false,
      or_false,if_false,zero_add]
    by_cases ix : s<Z i <;> by_cases jx : s<Z j <;>
      simp [StarScore.slot,RareScore.ind,bits,bothZero,bothOne,opposite,ix,jx]
  · rw [observedSlot,if_neg (mt hcomm.mp inC)]
    simp only [positive,commonPositive,span,inC,false_and,if_false,add_zero]
    by_cases left : f s<ε
    · have rr : r s=true := decide_eq_true (left.le.trans cut)
      have right : ¬1-ε<f s := by linarith
      by_cases ix : s<Z i <;> by_cases jx : s<Z j <;> by_cases ok : good s <;>
        simp [rarePositive,inside,inside.1,inside.2,left,right,
          RareScore.slot,RareScore.ind,RareScore.nonshared,rr,bits,selected,ok,ix,jx,bothZero,bothOne,opposite]
    · have right : 1-ε<f s := lt_of_not_ge (fun h => inC ⟨le_of_not_gt left,h⟩)
      have rr : r s=false := decide_eq_false (by linarith)
      by_cases ix : s<Z i <;> by_cases jx : s<Z j <;> by_cases ok : good s <;>
        simp [rarePositive,inside,inside.1,inside.2,left,right,
          RareScore.slot,RareScore.ind,RareScore.nonshared,rr,bits,selected,ok,ix,jx,bothZero,bothOne,opposite]

end
end PlanarUnitDistances.Flanks
