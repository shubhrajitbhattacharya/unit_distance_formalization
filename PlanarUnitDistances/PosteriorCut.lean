import PlanarUnitDistances.RareSlots
import PlanarUnitDistances.PosteriorComparison
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Averaging the two points in one posterior history class. Adapted from OAI Predictions and PredictionBudget. -/
namespace OAI
namespace PlanarUnitDistances.FiniteLaw
open Finset
noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]
def mix (μ : Law X) (ν : X → Law Y) : Law Y where
  val y := avg μ (fun x => (ν x).val y)
  nonneg _ := avg_nonneg _ (fun x => (ν x).nonneg _)
  total := by
    simp only [avg]
    rw [sum_comm]
    simp [← mul_sum,Law.total]

lemma mix_avg (μ : Law X) (ν : X → Law Y) (f : Y → ℝ) :
    avg (mix μ ν) f = avg μ (fun x => avg (ν x) f) := by
  simp only [avg,mix,sum_mul,mul_sum,mul_assoc]
  rw [sum_comm]

end
end PlanarUnitDistances.FiniteLaw
namespace PlanarUnitDistances.TemplateCollision
open Finset FiniteLaw
open scoped Classical
lemma collision_eq {X : Type*} [Fintype X] (μ : Law X) :
    event (pair μ μ) (fun xx => xx.1=xx.2)=∑x,μ.val x^2 := by
  simp [event,avg,pair,Fintype.sum_prod_type,pow_two]

end PlanarUnitDistances.TemplateCollision
namespace PlanarUnitDistances.PredictionCoupling
open Finset FiniteLaw FiniteMarginalScore
open scoped Classical
noncomputable section
variable {P H A B : Type*} [Fintype P] [Fintype H] [Fintype A] [Fintype B]

def coupling (μ : Law P) (h : P → H) : Law (P×P) :=
  mix (push μ h) (fun j => pair (cond μ h j) (cond μ h j))

lemma first (μ : Law P) (h : P → H) (f : P → ℝ) :
    avg (coupling μ h) (fun pp => f pp.1)=avg μ f := by
  rw [coupling,mix_avg]
  simp_rw [pair_fst]
  exact cond_tower μ h f
lemma second (μ : Law P) (h : P → H) (f : P → ℝ) :
    avg (coupling μ h) (fun pp => f pp.2)=avg μ f := by
  rw [coupling,mix_avg]
  simp_rw [pair_snd]
  exact cond_tower μ h f

lemma cond_diagonal (μ : Law P) (h : P → H) (j : H) {d : ℝ} (hd : 0 ≤ d)
    (hm : ∀p,μ.val p ≤ d) :
    (push μ h).val j*event (pair (cond μ h j) (cond μ h j)) (fun pp => pp.1=pp.2) ≤ d := by
  rw [TemplateCollision.collision_eq,mul_sum]
  calc
    _ = ∑p,(if h p=j then μ.val p else 0)*(cond μ h j).val p := by
      apply sum_congr rfl
      intro p _
      rw [pow_two,←mul_assoc]
      exact congrArg (fun t => t*(cond μ h j).val p) (cond_weight μ h j p)
    _ ≤ ∑p,d*(cond μ h j).val p := by
      apply sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_right (by split_ifs; exact hm p; exact hd) ((cond μ h j).nonneg p)
    _ = d := by rw [←mul_sum,(cond μ h j).total,mul_one]

theorem diagonal (μ : Law P) (h : P → H) {d : ℝ} (hd : 0 ≤ d) (hm : ∀p,μ.val p ≤ d) :
    event (coupling μ h) (fun pp => pp.1=pp.2) ≤ (Fintype.card H:ℝ)*d := by
  unfold event
  rw [coupling,mix_avg]
  calc
    _ ≤ ∑_j : H,d := sum_le_sum (fun j _ => cond_diagonal μ h j hd hm)
    _ = _ := by simp

lemma coordinate_collision (μ : Law P) (φ : P → A) :
    event (pair μ μ) (fun pp => φ pp.1=φ pp.2)=collision μ φ := by
  unfold event
  rw [pair_avg]
  have he : (fun p => avg μ (fun q => if φ p=φ q then (1:ℝ) else 0))=
      (fun p => fiberMass μ φ (φ p)) := by
    funext p
    exact event_congr μ (fun q => eq_comm)
  rw [he,←push_avg μ φ (fun a => fiberMass μ φ a)]
  simp only [avg,push,collision,fiberMass,pow_two]

lemma collision_push (μ : Law P) (x : P → A×B) :
    collision (push μ x) Prod.fst=collision μ (fun p => (x p).1) ∧
    collision (push μ x) Prod.snd=collision μ (fun p => (x p).2) := by
  constructor <;> unfold collision event <;> simp_rw [push_avg]

lemma tau_pair (μ : Law P) (x : P → A×B) :
    avg (pair μ μ) (fun pp => (if (x pp.1).1=(x pp.2).1 then 1 else 0)+
      (if (x pp.1).2=(x pp.2).2 then 1 else 0)-1)=tau (push μ x) := by
  rw [avg_sub,avg_add,avg_const]
  change event (pair μ μ) (fun pp => (x pp.1).1=(x pp.2).1)+
    event (pair μ μ) (fun pp => (x pp.1).2=(x pp.2).2)-1=_
  rw [coordinate_collision μ (fun p => (x p).1),coordinate_collision μ (fun p => (x p).2),tau,(collision_push μ x).1,(collision_push μ x).2]

theorem tau_eq (μ : Law P) (h : P → H) (x : P → A×B) :
    avg (coupling μ h) (fun pp => (if (x pp.1).1=(x pp.2).1 then 1 else 0)+
      (if (x pp.1).2=(x pp.2).2 then 1 else 0)-1)=
      avg μ (fun p => tau (push (cond μ h (h p)) x)) := by
  rw [coupling,mix_avg]
  simp_rw [tau_pair]
  exact push_avg μ h _
end
end PlanarUnitDistances.PredictionCoupling


namespace PlanarUnitDistances.FiniteLawIntegral
open Finset MeasureTheory FiniteLaw
open scoped Classical
variable {X Ω : Type*} [Fintype X] [MeasurableSpace Ω]
lemma integral_avg (μ : Law X) {ν : Measure Ω} (f : X → Ω → ℝ)
    (hf : ∀x,Integrable (f x) ν) :
    (∫a,avg μ (fun x => f x a) ∂ν)=avg μ (fun x => ∫a,f x a ∂ν) := by
  unfold avg
  rw [integral_finsetSum _ (fun x _ => (hf x).const_mul _)]
  simp only [integral_const_mul]

lemma avg_indicator_mul (μ : Law X) (P : X → Prop) (c : ℝ) :
    avg μ (fun x => if P x then c else 0)=c*event μ P := by
  unfold event
  rw [←avg_smul]
  apply avg_congr
  intro x
  split_ifs <;> ring
end PlanarUnitDistances.FiniteLawIntegral
namespace PlanarUnitDistances.PredictionCut
open Finset MeasureTheory FiniteLaw RareScore PredictionCoupling FiniteLawIntegral
open scoped Classical
noncomputable section
variable {P H A B Ω : Type*} [Fintype P] [Fintype H]

def pairScore (x y : A×B) : ℝ :=
  (if x.1=y.1 then 1 else 0)+(if x.2=y.2 then 1 else 0)-1
lemma pairScore_bounds (x y : A×B) : -1 ≤ pairScore x y ∧ pairScore x y ≤ 1 := by
  unfold pairScore
  split_ifs <;> norm_num
lemma pairScore_normal (r : Bool) (l x y : A×B)
    (hx : ¬exceptional r l x) (hy : ¬exceptional r l y) : 0 ≤ pairScore x y := by
  cases r <;> simp only [exceptional,Bool.false_eq_true, ↓reduceIte,not_not] at hx hy
  · have he : x.1=y.1 := hx.trans hy.symm
    unfold pairScore
    simp only [he,ite_true]
    split_ifs <;> norm_num
  · have he : x.2=y.2 := hx.trans hy.symm
    unfold pairScore
    simp only [he,ite_true]
    split_ifs <;> norm_num

lemma cut_bound (c g : Prop) (r : Bool) (l x y : A×B) :
    (if c then pairScore x y else 0) ≤ pairScore x y+
      ind (¬c ∧ g ∧ exceptional r l x)+ind (¬c ∧ g ∧ exceptional r l y)+ind (¬c ∧ ¬g) := by
  by_cases hc : c
  · simp [hc,ind]
  · by_cases hg : g
    · by_cases hx : exceptional r l x
      · simp only [hc,hg,hx,ind,↓reduceIte,true_and,not_false_eq_true,not_true_eq_false]
        have hb := (pairScore_bounds x y).1
        split_ifs <;> linarith
      · by_cases hy : exceptional r l y
        · simp only [hc,hg,hx,hy,ind,↓reduceIte,true_and,not_false_eq_true,not_true_eq_false]
          linarith [(pairScore_bounds x y).1]
        · simpa [hc,hg,hx,hy,ind] using pairScore_normal r l x y hx hy
    · simp only [hc,hg,ind,↓reduceIte,false_and,true_and,not_false_eq_true,add_zero]
      linarith [(pairScore_bounds x y).1]

variable [MeasurableSpace Ω]

theorem integrated (μ : Law P) (h : P → H) (ν : Measure Ω)
    (common good : Ω → Prop) (r : Ω → Bool) (l : Ω → A×B) (x : Ω → P → A×B)
    (C : ℝ) (hC : 0 ≤ C)
    (_hcommon : Integrable (fun a => ind (common a)) ν)
    (hbad : Integrable (fun a => ind (¬common a ∧ ¬good a)) ν)
    (hex : ∀p,Integrable (fun a => ind (¬common a ∧ good a ∧ exceptional (r a) (l a) (x a p))) ν)
    (hfull : ∀p q,Integrable (fun a => pairScore (x a p) (x a q)) ν)
    (hcut : ∀p q,Integrable (fun a => if common a then pairScore (x a p) (x a q) else 0) ν)
    (hbound : ∀p q,p≠q → (∫a,pairScore (x a p) (x a q) ∂ν) ≤ C)
    {d : ℝ} (hd : 0 ≤ d) (hm : ∀p,μ.val p ≤ d) :
    (∫a,avg (coupling μ h) (fun pp => if common a then pairScore (x a pp.1) (x a pp.2) else 0) ∂ν) ≤
      C+2*avg μ (fun p => ∫a,ind (¬common a ∧ good a ∧ exceptional (r a) (l a) (x a p)) ∂ν)+
      (∫a,ind (¬common a ∧ ¬good a) ∂ν)+
      (∫a,ind (common a) ∂ν)*((Fintype.card H:ℝ)*d) := by
  let e := fun p => ∫a,ind (¬common a ∧ good a ∧ exceptional (r a) (l a) (x a p)) ∂ν
  let wb := ∫a,ind (¬common a ∧ ¬good a) ∂ν
  let wc := ∫a,ind (common a) ∂ν
  have he0 (p : P) : 0 ≤ e p := integral_nonneg (fun a => ind_nonneg _)
  have hw0 : 0 ≤ wb := integral_nonneg (fun a => ind_nonneg _)
  have hc0 : 0 ≤ wc := integral_nonneg (fun a => ind_nonneg _)
  rw [integral_avg (coupling μ h) _ (fun pp => hcut pp.1 pp.2)]
  have hb (p q : P) : (∫a,if common a then pairScore (x a p) (x a q) else 0 ∂ν) ≤
      C+e p+e q+wb+(if p=q then wc else 0) := by
    by_cases hpq : p=q
    · subst q
      have hh : (∫a,if common a then pairScore (x a p) (x a p) else 0 ∂ν)=wc := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun a => by simp [pairScore,ind])
      rw [hh, if_pos rfl]
      linarith [he0 p]
    · rw [if_neg hpq,add_zero]
      have hh := integral_mono (hcut p q) (((hfull p q).add (hex p)).add (hex q) |>.add hbad)
        (fun a => cut_bound (common a) (good a) (r a) (l a) (x a p) (x a q))
      have hi₁ := integral_add (hfull p q) (hex p)
      have hi₂ := integral_add ((hfull p q).add (hex p)) (hex q)
      have hi₃ := integral_add (((hfull p q).add (hex p)).add (hex q)) hbad
      simp only [Pi.add_apply] at hh hi₁ hi₂ hi₃
      rw [hi₃,hi₂,hi₁] at hh
      exact hh.trans (by dsimp only [e,wb]; linarith [hbound p q hpq])
  have hh := avg_mono (coupling μ h) (fun pp => hb pp.1 pp.2)
  simp only [avg_add,avg_const,PredictionCoupling.first,PredictionCoupling.second,avg_indicator_mul] at hh
  have hdg := mul_le_mul_of_nonneg_left (PredictionCoupling.diagonal μ h hd hm) hc0
  change _ ≤ C+2*avg μ e+wb+wc*((Fintype.card H:ℝ)*d)
  linarith
end
end PlanarUnitDistances.PredictionCut

end OAI
