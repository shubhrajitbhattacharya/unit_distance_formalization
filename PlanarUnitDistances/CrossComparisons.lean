import PlanarUnitDistances.CrossScores

/-! Exact conditional score inequalities for the common levels. Adapted from
the OAI UnitDistances Transfer and Predictions modules. -/
namespace OAI
namespace PlanarUnitDistances.RestrictedTransfer
open Finset

section Supports
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def row (a : A) : Finset (A × B) := univ.filter (fun x => x.1 = a)
def col (b : B) : Finset (A × B) := univ.filter (fun x => x.2 = b)

def Permitted (U : Finset (A × B)) : Prop :=
  (∃ a, U = row a) ∨ (∃ b, U = col b) ∨ U.card ≤ 2

end Supports
end PlanarUnitDistances.RestrictedTransfer
namespace PlanarUnitDistances.CrossStructure
open Finset StrictCross RestrictedTransfer
open scoped Classical
noncomputable section
variable {A B : Type*}

def Consistent (b : Bool) (x y : A×B) : Prop :=
  if b then x.1=y.1 ∧ x.2≠y.2 else x.1≠y.1 ∧ x.2=y.2

lemma consistent_adj {b : Bool} {x y : A×B} (h : Consistent b x y) : Adj x y := by
  cases b with
  | false => exact Or.inr h
  | true => exact Or.inl h
lemma consistent_symm {b : Bool} {x y : A×B} (h : Consistent b x y) : Consistent b y x := by
  cases b <;> dsimp [Consistent] at *
  · exact ⟨Ne.symm h.1,Eq.symm h.2⟩
  · exact ⟨Eq.symm h.1,Ne.symm h.2⟩
lemma bit_unique {b c : Bool} {x y : A×B} (h : Consistent b x y) (h' : Consistent c x y) : b=c := by
  cases b <;> cases c <;> simp_all [Consistent]
lemma bit_true {b : Bool} {x y : A×B} (h : Consistent b x y) (he : x.1=y.1) : b=true := by
  cases b <;> simp_all [Consistent]
lemma bit_false {b : Bool} {x y : A×B} (h : Consistent b x y) (he : x.2=y.2) : b=false := by
  cases b <;> simp_all [Consistent]

def Shape (Y U : Finset (A×B)) : Prop :=
  (∀ y∈Y,∀ z∈Y,y=z) ∨ (∀ x∈U,∀ z∈U,x=z) ∨
  (∃ b : Bool,∀ x∈U,∀ y∈Y,∀ c,Consistent c x y → c=b) ∨
  ((∀ x∈U,∀ y∈Y,∀ z∈Y,∀ b,Consistent b x y → Consistent b x z → y=z) ∧
   (∀ y∈Y,∀ x∈U,∀ z∈U,∀ b,Consistent b x y → Consistent b z y → x=z))

lemma card_pair_le (y z : A×B) : ({y,z} : Finset (A×B)).card≤3 := by
  have := card_insert_le y {z}
  simp only [card_singleton] at this
  omega
lemma card_triple_le (y z w : A×B) : ({y,z,w} : Finset (A×B)).card≤3 := by
  have h := card_insert_le y {z,w}
  have h' := card_insert_le z {w}
  simp only [card_singleton] at h'
  omega

lemma pair_coord_inj {S : Finset (A×B)} {y z : A×B} (h : ∀w∈S,w=y ∨ w=z)
    (h₁ : y.1≠z.1) (h₂ : y.2≠z.2) :
    (∀u∈S,∀v∈S,u.1=v.1 → u=v) ∧ (∀u∈S,∀v∈S,u.2=v.2 → u=v) := by
  constructor <;> intro u hu v hv he
  · rcases h u hu with rfl|rfl <;> rcases h v hv with rfl|rfl
    · rfl
    · exact (h₁ he).elim
    · exact (h₁ he.symm).elim
    · rfl
  · rcases h u hu with rfl|rfl <;> rcases h v hv with rfl|rfl
    · rfl
    · exact (h₂ he).elim
    · exact (h₂ he.symm).elim
    · rfl

lemma determined_of_inj {S : Finset (A×B)}
    (h : (∀u∈S,∀v∈S,u.1=v.1 → u=v) ∧ (∀u∈S,∀v∈S,u.2=v.2 → u=v))
    (x : A×B) (y : A×B) (hy : y∈S) (z : A×B) (hz : z∈S) (b : Bool)
    (hc : Consistent b x y) (hd : Consistent b x z) : y=z := by
  cases b with
  | false => exact h.2 y hy z hz (hc.2.symm.trans hd.2)
  | true => exact h.1 y hy z hz (hc.1.symm.trans hd.1)

variable [Fintype A] [Fintype B]

theorem witnesses (Y : Finset (A×B)) :
    ∃ W U : Finset (A×B), W⊆Y ∧ W.card≤3 ∧ (U=univ ∨ Permitted U) ∧
      (∀x,(∀w∈W,Adj x w) → x∈U) ∧ Shape Y U := by
  classical
  rcases classification Y with h|h|h|h
  · refine ⟨∅,univ,empty_subset _,by simp,Or.inl rfl,fun x _ => mem_univ x,Or.inl ?_⟩
    exact card_le_one.mp h
  · obtain ⟨y,hy,z,hz,hyz,he,hw⟩ := h
    have hn : y.2≠z.2 := by intro hh; exact hyz (Prod.ext he hh)
    rcases hw with hall|⟨w,hw,hwy⟩
    · refine ⟨{y,z},row y.1,?_,card_pair_le y z,Or.inr (Or.inl ⟨y.1,rfl⟩),?_,?_⟩
      · simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hy hz
      · intro x hx
        have hx' := (same_row hn x).mp ⟨hx y (by simp),by simpa only [Adj,← he] using hx z (by simp)⟩
        simpa [row] using hx'.1
      · right; right; left
        refine ⟨true,?_⟩
        intro x hx v hv b hb
        have hx' : x.1=y.1 := by simpa [row] using hx
        exact bit_true hb (hx'.trans (hall v hv).symm)
    · refine ⟨{y,z,w},{(y.1,w.2)},?_,card_triple_le y z w,?_,?_,Or.inr (Or.inl ?_)⟩
      · simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hy (And.intro hz hw)
      · right; right; right; simp
      · intro x hx
        have hx' := third_off_row hn hwy.symm x (hx y (by simp))
          (by simpa only [Adj,← he] using hx z (by simp)) (hx w (by simp))
        exact mem_singleton.mpr hx'
      · intro x hx v hv
        exact (mem_singleton.mp hx).trans (mem_singleton.mp hv).symm
  · obtain ⟨y,hy,z,hz,hyz,he,hw⟩ := h
    have hn : y.1≠z.1 := by intro hh; exact hyz (Prod.ext hh he)
    rcases hw with hall|⟨w,hw,hwy⟩
    · refine ⟨{y,z},col y.2,?_,card_pair_le y z,Or.inr (Or.inr (Or.inl ⟨y.2,rfl⟩)),?_,?_⟩
      · simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hy hz
      · intro x hx
        have hx' := (same_column hn x).mp ⟨hx y (by simp),by simpa only [Adj,← he] using hx z (by simp)⟩
        simpa [col] using hx'.1
      · right; right; left
        refine ⟨false,?_⟩
        intro x hx v hv b hb
        have hx' : x.2=y.2 := by simpa [col] using hx
        exact bit_false hb (hx'.trans (hall v hv).symm)
    · refine ⟨{y,z,w},{(w.1,y.2)},?_,card_triple_le y z w,?_,?_,Or.inr (Or.inl ?_)⟩
      · simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hy (And.intro hz hw)
      · right; right; right; simp
      · intro x hx
        have hxy := (swap_iff x y).mpr (hx y (by simp))
        have hxz := (swap_iff x z).mpr (hx z (by simp))
        have hxw := (swap_iff x w).mpr (hx w (by simp))
        have hx' := third_off_row hn hwy.symm x.swap hxy
          (by simpa only [Prod.swap,← he] using hxz) hxw
        apply mem_singleton.mpr
        exact Prod.ext (congrArg Prod.snd hx') (congrArg Prod.fst hx')
      · intro x hx v hv
        exact (mem_singleton.mp hx).trans (mem_singleton.mp hv).symm
  · obtain ⟨y,hy,z,hz,h₁,h₂,hw⟩ := h
    rcases hw with hall|⟨w,hw,hyw,hzw,hyw',hzw'⟩
    · refine ⟨{y,z},{(y.1,z.2),(z.1,y.2)},?_,card_pair_le y z,?_,?_,?_⟩
      · simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hy hz
      · right; right; right
        exact (card_insert_le _ _).trans (by simp)
      · intro x hx
        simpa only [mem_insert,mem_singleton] using (corners h₁ h₂ x).mp ⟨hx y (by simp),hx z (by simp)⟩
      · right; right; right
        have hY := pair_coord_inj hall h₁ h₂
        have hU := pair_coord_inj (y := (y.1,z.2)) (z := (z.1,y.2)) (S := {(y.1,z.2),(z.1,y.2)})
          (by intro v hv; simpa only [mem_insert,mem_singleton] using hv) h₁ h₂.symm
        constructor
        · intro x _ u hu v hv b hc hd
          exact determined_of_inj hY x u hu v hv b hc hd
        · intro v _ x hx u hu b hc hd
          exact determined_of_inj hU v x hx u hu b (consistent_symm hc) (consistent_symm hd)
    · refine ⟨{y,z,w},∅,?_,card_triple_le y z w,?_,?_,Or.inr (Or.inl ?_)⟩
      · simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hy (And.intro hz hw)
      · right; right; right; simp
      · intro x hx
        exact (three_independent h₁ hyw hzw h₂ hyw' hzw' x
          ⟨hx y (by simp),hx z (by simp),hx w (by simp)⟩).elim
      · simp
end
end PlanarUnitDistances.CrossStructure

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]
lemma cond_tower_dep (μ : Law X) (φ : X → Y) (f : Y → X → ℝ) :
    avg (push μ φ) (fun y => avg (cond μ φ y) (f y)) = avg μ (fun x => f (φ x) x) := by
  classical
  unfold avg
  simp only [push,mul_sum,← mul_assoc,cond_weight]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [ite_mul,zero_mul]
  simp
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.FiniteStarCoupling
open Finset FiniteLaw StarScore CrossStructure
open scoped Classical
noncomputable section
variable {P Q A B : Type*} [Fintype P] [Fintype Q]

def left (π : Law (P×Q)) : Law P := push π Prod.fst
def right (π : Law (P×Q)) : Law Q := push π Prod.snd
def row (π : Law (P×Q)) (p : P) : Law Q := push (cond π Prod.fst p) Prod.snd
def col (π : Law (P×Q)) (q : Q) : Law P := push (cond π Prod.snd q) Prod.fst

lemma row_avg (π : Law (P×Q)) (f : P → Q → ℝ) :
    avg (left π) (fun p => avg (row π p) (f p)) = avg π (fun pq => f pq.1 pq.2) := by
  simp only [row,push_avg]
  change avg (push π Prod.fst) _ = _
  exact cond_tower_dep π Prod.fst (fun p pq => f p pq.2)
lemma col_avg (π : Law (P×Q)) (f : P → Q → ℝ) :
    avg (right π) (fun q => avg (col π q) (fun p => f p q)) = avg π (fun pq => f pq.1 pq.2) := by
  simp only [col,push_avg]
  change avg (push π Prod.snd) _ = _
  exact cond_tower_dep π Prod.snd (fun q pq => f pq.1 q)
lemma row_event (π : Law (P×Q)) (g : P → Q → Prop) :
    avg (left π) (fun p => event (row π p) (g p)) = event π (fun pq => g pq.1 pq.2) := by
  unfold event
  exact row_avg π _
lemma col_event (π : Law (P×Q)) (g : P → Q → Prop) :
    avg (right π) (fun q => event (col π q) (fun p => g p q)) = event π (fun pq => g pq.1 pq.2) := by
  unfold event
  exact col_avg π _

def DP (π : Law (P×Q)) (bit : P → Q → Bool) (y : Q → A×B) : ℝ :=
  avg (left π) (fun p => score (row π p) (bit p) y)
def DQ (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) : ℝ :=
  avg (right π) (fun q => score (col π q) (fun p => bit p q) x)
def VP (π : Law (P×Q)) (bit : P → Q → Bool) : ℝ :=
  avg (left π) (fun p => variation (row π p) (bit p))
def VQ (π : Law (P×Q)) (bit : P → Q → Bool) : ℝ :=
  avg (right π) (fun q => variation (col π q) (fun p => bit p q))
def bad (π : Law (P×Q)) (good : P → Q → Prop) : ℝ := event π (fun pq => ¬good pq.1 pq.2)

lemma vp_le (π : Law (P×Q)) (bit : P → Q → Bool) : VP π bit ≤ 1/2 :=
  avg_le_const _ (fun p => variation_le_half (row π p) (bit p))
lemma vq_le (π : Law (P×Q)) (bit : P → Q → Bool) : VQ π bit ≤ 1/2 :=
  avg_le_const _ (fun q => variation_le_half (col π q) (fun p => bit p q))
lemma dp_lower (π : Law (P×Q)) (bit : P → Q → Bool) (y : Q → A×B) : -VP π bit ≤ DP π bit y := by
  have h := avg_mono (left π) (fun p => score_lower (row π p) (bit p) y)
  have he : avg (left π) (fun p => -variation (row π p) (bit p)) = -VP π bit := by
    calc
      _ = avg (left π) (fun p => (-1)*variation (row π p) (bit p)) :=
        avg_congr _ (fun p => by ring)
      _ = _ := by rw [avg_smul]; simp only [neg_one_mul,VP]
  exact he ▸ h
lemma dq_lower (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) : -VQ π bit ≤ DQ π bit x := by
  have h := avg_mono (right π) (fun q => score_lower (col π q) (fun p => bit p q) x)
  have he : avg (right π) (fun q => -variation (col π q) (fun p => bit p q)) = -VQ π bit := by
    calc
      _ = avg (right π) (fun q => (-1)*variation (col π q) (fun p => bit p q)) :=
        avg_congr _ (fun q => by ring)
      _ = _ := by rw [avg_smul]; simp only [neg_one_mul,VQ]
  exact he ▸ h

theorem slice_score (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B)
    (good : P → Q → Prop) (Y U : Finset (A×B)) (hs : Shape Y U)
    (hg : ∀ p q,good p q → x p∈U ∧ y q∈Y ∧ Consistent (bit p q) (x p) (y q)) :
    (VP π bit+VQ π bit)/6-16*bad π good ≤ DP π bit y+DQ π bit x := by
  have hbad : 0≤bad π good := event_nonneg _ _
  have hvp := vp_le π bit
  have hvq := vq_le π bit
  have hdp := dp_lower π bit y
  have hdq := dq_lower π bit x
  rcases hs with hs|hs|⟨b,hs⟩|⟨hsP,hsQ⟩
  · have h (p : P) := constant_good (row π p) (bit p) y (good p) (by
      intro q r hq hr
      have hy := hs (y q) (hg p q hq).2.1 (y r) (hg p r hr).2.1
      refine ⟨?_,hy⟩
      exact bit_unique (hg p q hq).2.2 (hy ▸ (hg p r hr).2.2))
    have ha := avg_mono (left π) h
    rw [avg_sub,avg_const,avg_smul,row_event] at ha
    change (1-1/6:ℝ)-4*bad π good ≤ DP π bit y at ha
    linarith
  · have h (q : Q) := constant_good (col π q) (fun p => bit p q) x (fun p => good p q) (by
      intro p r hp hr
      have hx := hs (x p) (hg p q hp).1 (x r) (hg r q hr).1
      refine ⟨?_,hx⟩
      exact bit_unique (hg p q hp).2.2 (hx ▸ (hg r q hr).2.2))
    have ha := avg_mono (right π) h
    rw [avg_sub,avg_const,avg_smul,col_event] at ha
    change (1-1/6:ℝ)-4*bad π good ≤ DQ π bit x at ha
    linarith
  · have hc : ∀p q,good p q → bit p q=b := by
      intro p q hp
      exact hs (x p) (hg p q hp).1 (y q) (hg p q hp).2.1 _ (hg p q hp).2.2
    have hp := avg_mono (left π) (fun p => constant_bit (row π p) (bit p) (good p)
      (by intro q r hq hr; exact (hc p q hq).trans (hc p r hr).symm))
    have hq := avg_mono (right π) (fun q => constant_bit (col π q) (fun p => bit p q) (fun p => good p q)
      (by intro p r hp hr; exact (hc p q hp).trans (hc r q hr).symm))
    rw [avg_smul,row_event] at hp
    rw [avg_smul,col_event] at hq
    change VP π bit ≤ 2*bad π good at hp
    change VQ π bit ≤ 2*bad π good at hq
    linarith
  · have hp := avg_mono (left π) (fun p => determined (row π p) (bit p) y (good p) (by
      intro q r hq hr hb
      apply hsP (x p) (hg p q hq).1 (y q) (hg p q hq).2.1 (y r) (hg p r hr).2.1 (bit p q)
      · exact (hg p q hq).2.2
      · exact hb ▸ (hg p r hr).2.2))
    have hq := avg_mono (right π) (fun q => determined (col π q) (fun p => bit p q) x (fun p => good p q) (by
      intro p r hp hr hb
      apply hsQ (y q) (hg p q hp).2.1 (x p) (hg p q hp).1 (x r) (hg r q hr).1 (bit p q)
      · exact (hg p q hp).2.2
      · exact hb ▸ (hg r q hr).2.2))
    simp only [div_eq_mul_inv, mul_comm _ (6:ℝ)⁻¹,avg_sub,avg_smul,row_event] at hp
    simp only [div_eq_mul_inv, mul_comm _ (6:ℝ)⁻¹,avg_sub,avg_smul,col_event] at hq
    change (6:ℝ)⁻¹*VP π bit-6*bad π good ≤ DP π bit y at hp
    change (6:ℝ)⁻¹*VQ π bit-6*bad π good ≤ DQ π bit x at hq
    linarith
end
end PlanarUnitDistances.FiniteStarCoupling
namespace PlanarUnitDistances.FiniteLaw
variable {X : Type*} [Fintype X]
lemma event_congr (μ : Law X) {P Q : X → Prop} (h : ∀ x,P x ↔ Q x) :
    event μ P=event μ Q := le_antisymm (event_mono μ (fun x => (h x).mp))
      (event_mono μ (fun x => (h x).mpr))

lemma event_true (μ : Law X) : event μ (fun _ => True)=1 := by
  simp [event,avg_const]

end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.CrossSampling
open Finset FiniteLaw StrictCross
open scoped Classical
noncomputable section
variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I] [DecidableEq I]

def crossMass (ν : Law (A×B)) (y : A×B) : ℝ := event ν (fun x => Adj x y)
def rowMass (ν : Law (A×B)) (a : A) : ℝ := event ν (fun x => x.1=a)
def colMass (ν : Law (A×B)) (b : B) : ℝ := event ν (fun x => x.2=b)

end
end PlanarUnitDistances.CrossSampling
namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X : Type*} [Fintype X]
lemma event_and_lower (μ : Law X) (P Q : X → Prop) :
    event μ P+event μ Q-1 ≤ event μ (fun x => P x∧Q x) := by
  have h := avg_mono μ (f := fun x => (if P x then (1:ℝ) else 0)+(if Q x then (1:ℝ) else 0)-1)
    (g := fun x => if P x∧Q x then (1:ℝ) else 0) (fun x => by split_ifs <;> simp_all)
  simpa only [avg_sub,avg_add,avg_const,avg_ite] using h
lemma event_disjoint_union (μ : Law X) (P Q : X → Prop) (h : ∀x,¬(P x∧Q x)) :
    event μ (fun x => P x∨Q x)=event μ P+event μ Q := by
  unfold event
  rw [← avg_add]
  apply avg_congr
  intro x
  have := h x
  split_ifs <;> simp_all
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.FiniteMarginalScore
open Finset FiniteLaw StrictCross CrossStructure CrossSampling StarScore
open scoped Classical
noncomputable section
variable {A B Q : Type*} [Fintype A] [Fintype B] [Fintype Q]

def collision {X Y : Type*} [Fintype X] [Fintype Y] (ν : Law X) (φ : X → Y) : ℝ :=
  ∑ y,(event ν (fun x => φ x=y))^2

def tau (ν : Law (A×B)) : ℝ := collision ν Prod.fst+collision ν Prod.snd-1

lemma collision_nonneg {X Y : Type*} [Fintype X] [Fintype Y] (ν : Law X) (φ : X → Y) :
    0≤collision ν φ := sum_nonneg fun _ _ => sq_nonneg _
lemma collision_atom {X Y : Type*} [Fintype X] [Fintype Y] (ν : Law X) (φ : X → Y) (a : Y) :
    event ν (fun x => φ x=a)^2 ≤ collision ν φ := by
  unfold collision
  exact single_le_sum (f := fun y => (event ν (fun x => φ x=y))^2) (fun _ _ => sq_nonneg _) (mem_univ a)
lemma collision_two {X Y : Type*} [Fintype X] [Fintype Y] (ν : Law X) (φ : X → Y)
    {a b : Y} (hab : a≠b) :
    event ν (fun x => φ x=a)^2+event ν (fun x => φ x=b)^2 ≤ collision ν φ := by
  have h := sum_le_sum_of_subset_of_nonneg (show ({a,b}:Finset Y)⊆univ from subset_univ _)
    (f := fun y => event ν (fun x => φ x=y)^2) (fun _ _ _ => sq_nonneg _)
  simpa [collision,hab] using h
lemma collision_one_linear {X Y : Type*} [Fintype X] [Fintype Y] (ν : Law X) (φ : X → Y) (a : Y) :
    2*event ν (fun x => φ x=a)-1≤collision ν φ := by
  have h := collision_atom ν φ a
  nlinarith [sq_nonneg (event ν (fun x => φ x=a)-1)]
lemma collision_two_linear {X Y : Type*} [Fintype X] [Fintype Y] (ν : Law X) (φ : X → Y)
    {a b : Y} (hab : a≠b) :
    event ν (fun x => φ x=a)+event ν (fun x => φ x=b)-1/2≤collision ν φ := by
  have h := collision_two ν φ hab
  nlinarith [sq_nonneg (event ν (fun x => φ x=a)+event ν (fun x => φ x=b)-1),
    sq_nonneg (event ν (fun x => φ x=a)-event ν (fun x => φ x=b))]

lemma tau_lower (ν : Law (A×B)) : -1≤tau ν := by
  unfold tau
  linarith [collision_nonneg ν Prod.fst,collision_nonneg ν Prod.snd]
lemma tau_row (ν : Law (A×B)) (a : A) : 2*rowMass ν a-2≤tau ν := by
  have h := collision_one_linear ν Prod.fst a
  have h' := collision_nonneg ν Prod.snd
  change 2*rowMass ν a-1≤collision ν Prod.fst at h
  unfold tau
  linarith
lemma tau_col (ν : Law (A×B)) (b : B) : 2*colMass ν b-2≤tau ν := by
  have h := collision_one_linear ν Prod.snd b
  have h' := collision_nonneg ν Prod.fst
  change 2*colMass ν b-1≤collision ν Prod.snd at h
  unfold tau
  linarith
lemma tau_cross (ν : Law (A×B)) (y : A×B) : crossMass ν y-3/2≤tau ν := by
  have hA := collision_atom ν Prod.fst y.1
  have hB := collision_atom ν Prod.snd y.2
  have hm : crossMass ν y ≤ rowMass ν y.1+colMass ν y.2 :=
    (event_mono ν (fun x hx => hx.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2))).trans
      (event_union_le ν (fun x => x.1=y.1) (fun x => x.2=y.2))
  change rowMass ν y.1 ^ 2 ≤ _ at hA
  change colMass ν y.2 ^ 2 ≤ _ at hB
  unfold tau
  nlinarith [sq_nonneg (rowMass ν y.1+colMass ν y.2-1),sq_nonneg (rowMass ν y.1-colMass ν y.2)]
lemma tau_atom (ν : Law (A×B)) (y : A×B) :
    4*event ν (fun x => x=y)-3≤tau ν := by
  have hA := collision_one_linear ν Prod.fst y.1
  have hB := collision_one_linear ν Prod.snd y.2
  have hmA := event_mono ν (fun x (hx : x=y) => congrArg Prod.fst hx)
  have hmB := event_mono ν (fun x (hx : x=y) => congrArg Prod.snd hx)
  unfold tau
  linarith
lemma tau_two (ν : Law (A×B)) {y z : A×B} (hA : y.1≠z.1) (hB : y.2≠z.2) :
    2*event ν (fun x => x=y∨x=z)-2≤tau ν := by
  have ha := collision_two_linear ν Prod.fst hA
  have hb := collision_two_linear ν Prod.snd hB
  have hmA := event_mono ν (fun x (hx : x=y∨x=z) => hx.elim
    (fun h => Or.inl (congrArg Prod.fst h)) (fun h => Or.inr (congrArg Prod.fst h)))
  have hmB := event_mono ν (fun x (hx : x=y∨x=z) => hx.elim
    (fun h => Or.inl (congrArg Prod.snd h)) (fun h => Or.inr (congrArg Prod.snd h)))
  rw [event_disjoint_union ν (fun x => x.1=y.1) (fun x => x.1=z.1)
    (fun x h => hA (h.1.symm.trans h.2))] at hmA
  rw [event_disjoint_union ν (fun x => x.2=y.2) (fun x => x.2=z.2)
    (fun x h => hB (h.1.symm.trans h.2))] at hmB
  unfold tau
  linarith

lemma two_cross_mass (ν : Law (A×B)) {ε : ℝ} {y z : A×B}
    (hy : 1-ε≤crossMass ν y) (hz : 1-ε≤crossMass ν z) :
    1-2*ε≤event ν (fun x => Adj x y∧Adj x z) := by
  have h := event_and_lower ν (fun x => Adj x y) (fun x => Adj x z)
  change crossMass ν y+crossMass ν z-1≤_ at h
  linarith
lemma three_cross_mass (ν : Law (A×B)) {ε : ℝ} {y z w : A×B}
    (hy : 1-ε≤crossMass ν y) (hz : 1-ε≤crossMass ν z) (hw : 1-ε≤crossMass ν w) :
    1-3*ε≤event ν (fun x => Adj x y∧Adj x z∧Adj x w) := by
  have h₁ := two_cross_mass ν hz hw
  have h₂ := event_and_lower ν (fun x => Adj x y) (fun x => Adj x z∧Adj x w)
  change crossMass ν y+event ν (fun x => Adj x z∧Adj x w)-1≤_ at h₂
  linarith

theorem second_slice (μ : Law Q) (bit : Q → Bool) (state : Q → A×B)
    (ν : Law (A×B)) (x : A×B) (good : Q → Prop) {ε : ℝ} (hε : 0≤ε)
    (hcons : ∀q,good q → Consistent (bit q) x (state q))
    (hprob : ∀q,good q → 1-ε≤crossMass ν (state q)) :
    variation μ bit/6-16*(event μ (fun q => ¬good q)+ε) ≤ score μ bit state+tau ν := by
  let b := event μ (fun q => ¬good q)
  let v := variation μ bit
  let d := score μ bit state
  have hb : 0≤b := event_nonneg _ _
  have hv : v≤1/2 := variation_le_half _ _
  have hd : -v≤d := score_lower _ _ _
  have hd' : -1/2≤d := by simpa only [neg_div] using score_ge_half_neg μ bit state
  have ht := tau_lower ν
  change v/6-16*(b+ε)≤d+tau ν
  by_cases hg : ∃q,good q
  swap
  · have he : b=1 := by
      dsimp [b]
      calc
        _ = event μ (fun _ => True) := event_congr _ (fun q => by simp only [not_exists] at hg; simp [hg q])
        _ = 1 := event_true _
    rw [he]
    linarith
  obtain ⟨q₀,hq₀⟩ := hg
  let Y := (univ.filter good).image state
  have memY {y : A×B} : y∈Y ↔ ∃q,good q ∧ state q=y := by simp only [Y,mem_image,mem_filter,mem_univ,true_and]
  have hmem (q : Q) (hq : good q) : state q∈Y := memY.mpr ⟨q,hq,rfl⟩
  have hx (y : A×B) (hy : y∈Y) : Adj x y := by
    obtain ⟨q,hq,rfl⟩ := memY.mp hy
    exact consistent_adj (hcons q hq)
  have hm (y : A×B) (hy : y∈Y) : 1-ε≤crossMass ν y := by
    obtain ⟨q,hq,rfl⟩ := memY.mp hy
    exact hprob q hq
  rcases classification Y with hs|hs|hs|hs
  · have hd₁ := constant_good μ bit state good (by
      intro q r hq hr
      have he := card_le_one.mp hs _ (hmem q hq) _ (hmem r hr)
      exact ⟨bit_unique (hcons q hq) (he ▸ hcons r hr),he⟩)
    have ht₁ := tau_cross ν (state q₀)
    have ht₂ := hprob q₀ hq₀
    change (1-1/6:ℝ)-4*b≤d at hd₁
    linarith
  · obtain ⟨y,hy,z,hz,hyz,he,hw⟩ := hs
    have hn : y.2≠z.2 := by intro hh; exact hyz (Prod.ext he hh)
    have hzx : Adj x (y.1,z.2) := by simpa only [Adj,←he] using hx z hz
    have hxr : x.1=y.1 := ((same_row hn x).mp ⟨hx y hy,hzx⟩).1
    have hr : 1-2*ε≤rowMass ν y.1 := by
      refine (two_cross_mass ν (hm y hy) (hm z hz)).trans (event_mono ν ?_)
      intro u hu
      exact ((same_row hn u).mp ⟨hu.1,by simpa only [Adj,←he] using hu.2⟩).1
    rcases hw with hall|⟨w,hw,hwy⟩
    · have hc : ∀q,good q → bit q=true := by
        intro q hq
        exact bit_true (hcons q hq) (hxr.trans (hall _ (hmem q hq)).symm)
      have hcv := constant_bit μ bit good (fun q r hq hr => (hc q hq).trans (hc r hr).symm)
      have ht₁ := tau_row ν y.1
      change v≤2*b at hcv
      linarith
    · have ha : 1-3*ε≤event ν (fun u => u=(y.1,w.2)) := by
        refine (three_cross_mass ν (hm y hy) (hm z hz) (hm w hw)).trans (event_mono ν ?_)
        intro u hu
        exact third_off_row hn hwy.symm u hu.1 (by simpa only [Adj,←he] using hu.2.1) hu.2.2
      have ht₁ := tau_atom ν (y.1,w.2)
      linarith
  · obtain ⟨y,hy,z,hz,hyz,he,hw⟩ := hs
    have hn : y.1≠z.1 := by intro hh; exact hyz (Prod.ext hh he)
    have hzx : Adj x (z.1,y.2) := by simpa only [Adj,←he] using hx z hz
    have hxc : x.2=y.2 := ((same_column hn x).mp ⟨hx y hy,hzx⟩).1
    have hr : 1-2*ε≤colMass ν y.2 := by
      refine (two_cross_mass ν (hm y hy) (hm z hz)).trans (event_mono ν ?_)
      intro u hu
      exact ((same_column hn u).mp ⟨hu.1,by simpa only [Adj,←he] using hu.2⟩).1
    rcases hw with hall|⟨w,hw,hwy⟩
    · have hc : ∀q,good q → bit q=false := by
        intro q hq
        exact bit_false (hcons q hq) (hxc.trans (hall _ (hmem q hq)).symm)
      have hcv := constant_bit μ bit good (fun q r hq hr => (hc q hq).trans (hc r hr).symm)
      have ht₁ := tau_col ν y.2
      change v≤2*b at hcv
      linarith
    · have ha : 1-3*ε≤event ν (fun u => u=(w.1,y.2)) := by
        refine (three_cross_mass ν (hm y hy) (hm z hz) (hm w hw)).trans (event_mono ν ?_)
        intro u hu
        have huy := (swap_iff u y).mpr hu.1
        have huz := (swap_iff u z).mpr hu.2.1
        have huw := (swap_iff u w).mpr hu.2.2
        have he' := third_off_row hn hwy.symm u.swap huy
          (by simpa only [Prod.swap,←he] using huz) huw
        exact Prod.ext (congrArg Prod.snd he') (congrArg Prod.fst he')
      have ht₁ := tau_atom ν (w.1,y.2)
      linarith
  · obtain ⟨y,hy,z,hz,h₁,h₂,hw⟩ := hs
    rcases hw with hall|⟨w,hw,hyw,hzw,hyw',hzw'⟩
    · have ha : 1-2*ε≤event ν (fun u => u=(y.1,z.2)∨u=(z.1,y.2)) := by
        refine (two_cross_mass ν (hm y hy) (hm z hz)).trans (event_mono ν ?_)
        intro u hu
        exact (corners h₁ h₂ u).mp hu
      have ht₁ := tau_two ν (y := (y.1,z.2)) (z := (z.1,y.2)) h₁ h₂.symm
      have hinj := pair_coord_inj hall h₁ h₂
      have hdet := determined μ bit state good (by
        intro q r hq hr hbit
        exact determined_of_inj hinj x (state q) (hmem q hq) (state r) (hmem r hr)
          (bit q) (hcons q hq) (hbit ▸ hcons r hr))
      change v/6-6*b≤d at hdet
      linarith
    · exact (three_independent h₁ hyw hzw h₂ hyw' hzw' x ⟨hx y hy,hx z hz,hx w hw⟩).elim
end
end PlanarUnitDistances.FiniteMarginalScore


end OAI
