import PlanarUnitDistances.CrossComparisons

/-! Rare score and endpoint profile inequalities on actual pairs of independent neighbors. Adapted from OAI Transfer. -/
namespace OAI
namespace PlanarUnitDistances.RareScore
open FiniteLaw CrossStructure
open scoped Classical
noncomputable section
variable {A B X : Type*}

def exceptional (r : Bool) (l x : A×B) : Prop :=
  if r then x.2≠l.2 else x.1≠l.1

def nonshared (b : Bool) (y z : A×B) : Prop :=
  if b then y.2=z.2 else y.1=z.1

lemma normal_bits {r b c : Bool} {l x y z : A×B}
    (hy : ¬exceptional r l y) (hz : ¬exceptional r l z)
    (hb : Consistent b x y) (hc : Consistent c x z) : b=c := by
  cases r <;> cases b <;> cases c <;>
    simp_all [exceptional,Consistent]

lemma exceptional_bits {r b c : Bool} {l x y z : A×B}
    (hx : exceptional r l x) (hy : ¬exceptional r l y) (hz : ¬exceptional r l z)
    (hb : Consistent b x y) (hc : Consistent c x z) :
    b=r ∧ c=r ∧ nonshared r y z := by
  cases r <;> cases b <;> cases c <;>
    simp_all [exceptional,Consistent,nonshared]

lemma minority_exception {r b : Bool} {l x y : A×B}
    (hb : Consistent b x y) (hr : b=r) : exceptional r l x ∨ exceptional r l y := by
  subst b
  cases r <;> simp only [exceptional,Consistent,Bool.false_eq_true, ↓reduceIte] at *
  · by_contra! h; exact hb.1 (h.1.trans h.2.symm)
  · by_contra! h; exact hb.2 (h.1.trans h.2.symm)

def ind (h : Prop) : ℝ := if h then 1 else 0
lemma ind_nonneg (h : Prop) : 0≤ ind h := by unfold ind; split_ifs <;> norm_num

def slot (r : Bool) (l x y z : A×B) (b c : Bool) : ℝ :=
  2*ind (exceptional r l x ∧ b=r ∧ c=r ∧ nonshared r y z)-ind (b≠c)

lemma slot_lower (r : Bool) (l x y z : A×B) (b c : Bool) :
    2*ind (exceptional r l x)-2*ind (exceptional r l x ∧ exceptional r l y)-
      2*ind (exceptional r l x ∧ exceptional r l z)-ind (exceptional r l y)-
      ind (exceptional r l z)-3*ind (¬Consistent b x y)-3*ind (¬Consistent c x z) ≤
    slot r l x y z b c := by
  have hp := exceptional_bits (r:=r) (b:=b) (c:=c) (l:=l) (x:=x) (y:=y) (z:=z)
  have hn := normal_bits (r:=r) (b:=b) (c:=c) (l:=l) (x:=x) (y:=y) (z:=z)
  have hpos : 2*ind (exceptional r l x)-
      2*ind (exceptional r l x ∧ exceptional r l y)-
      2*ind (exceptional r l x ∧ exceptional r l z)-
      2*ind (¬Consistent b x y)-2*ind (¬Consistent c x z) ≤
      2*ind (exceptional r l x ∧ b=r ∧ c=r ∧ nonshared r y z) := by
    unfold ind
    split_ifs <;> simp_all <;> norm_num
  have hneg : ind (b≠c)≤ ind (exceptional r l y)+ind (exceptional r l z)+
      ind (¬Consistent b x y)+ind (¬Consistent c x z) := by
    unfold ind
    split_ifs <;> simp_all <;> norm_num
  unfold slot
  linarith

variable [Fintype X]

theorem star_lower (μ : Law X) (r : Bool) (l base : A×B)
    (state : X → A×B) (bit : X → Bool) :
    2*ind (exceptional r l base)-
      4*event μ (fun y => exceptional r l base ∧ exceptional r l (state y))-
      2*event μ (fun y => exceptional r l (state y))-
      6*event μ (fun y => ¬Consistent (bit y) base (state y)) ≤
    avg (pair μ μ) (fun yz => slot r l base (state yz.1) (state yz.2) (bit yz.1) (bit yz.2)) := by
  have hs := avg_mono (pair μ μ) (fun yz =>
    slot_lower r l base (state yz.1) (state yz.2) (bit yz.1) (bit yz.2))
  simp only [avg_sub,avg_smul,avg_const] at hs
  have hf (g : X → Prop) : avg (pair μ μ) (fun yz => ind (g yz.1))=event μ g := by
    rw [pair_fst μ μ (fun x => ind (g x))]
    exact avg_ite μ g
  have hg (g : X → Prop) : avg (pair μ μ) (fun yz => ind (g yz.2))=event μ g := by
    rw [pair_snd μ μ (fun x => ind (g x))]
    exact avg_ite μ g
  rw [hf (fun y => exceptional r l base ∧ exceptional r l (state y)),
    hg (fun y => exceptional r l base ∧ exceptional r l (state y)),
    hf (fun y => exceptional r l (state y)),hg (fun y => exceptional r l (state y)),
    hf (fun y => ¬Consistent (bit y) base (state y)),
    hg (fun y => ¬Consistent (bit y) base (state y))] at hs
  linarith

end
end PlanarUnitDistances.RareScore

namespace PlanarUnitDistances.WedgeProfiles
open RareScore CrossStructure FiniteLaw
open scoped Classical
noncomputable section
variable {A B : Type*}


end
end PlanarUnitDistances.WedgeProfiles


end OAI
