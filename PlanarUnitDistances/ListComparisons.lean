import PlanarUnitDistances.CrossComparisons

/-! The actual one-edge law conditional on an independently sampled center list. Adapted from OAI Wedges. -/

namespace OAI

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

def dependent (μ : Law X) (ν : X → Law Y) : Law (X×Y) where
  val xy := μ.val xy.1*(ν xy.1).val xy.2
  nonneg xy := mul_nonneg (μ.nonneg _) ((ν _).nonneg _)
  total := by simp [Fintype.sum_prod_type,← mul_sum,Law.total]

lemma dependent_avg (μ : Law X) (ν : X → Law Y) (f : X×Y → ℝ) :
    avg (dependent μ ν) f = avg μ (fun x => avg (ν x) (fun y => f (x,y))) := by
  simp [avg,dependent,Fintype.sum_prod_type,mul_sum,mul_assoc]
lemma law_ext {μ ν : Law X} (h : ∀x,μ.val x=ν.val x) : μ=ν := by
  cases μ with | mk a ha sa =>
    cases ν with | mk b hb sb =>
      have : a=b := funext h
      subst b
      rfl
end
end PlanarUnitDistances.FiniteLaw
namespace PlanarUnitDistances.FiniteStarCoupling
open Finset FiniteLaw
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]
lemma left_val (π : Law (P×Q)) (p : P) : (left π).val p = ∑q,π.val (p,q) := by
  simp only [left,push,fiberMass_eq,Fintype.sum_prod_type]
  rw [sum_comm]
  simp
lemma right_val (π : Law (P×Q)) (q : Q) : (right π).val q = ∑p,π.val (p,q) := by
  simp [right,push,fiberMass_eq,Fintype.sum_prod_type]
lemma row_weight (π : Law (P×Q)) (p : P) (q : Q) :
    (left π).val p*(row π p).val q=π.val (p,q) := by
  simp only [row,push,fiberMass_eq,mul_sum]
  simp_rw [mul_ite,mul_zero]
  change (∑x : P×Q,if x.2=q then fiberMass π Prod.fst p*(cond π Prod.fst p).val x else 0)=_
  simp_rw [cond_weight]
  simp [Fintype.sum_prod_type]
lemma col_weight (π : Law (P×Q)) (p : P) (q : Q) :
    (right π).val q*(col π q).val p=π.val (p,q) := by
  simp only [col,push,fiberMass_eq,mul_sum]
  simp_rw [mul_ite,mul_zero]
  change (∑x : P×Q,if x.1=p then fiberMass π Prod.snd q*(cond π Prod.snd q).val x else 0)=_
  simp_rw [cond_weight]
  simp [Fintype.sum_prod_type]
lemma row_val (π : Law (P×Q)) {p : P} (hp : 0<(left π).val p) (q : Q) :
    (row π p).val q=π.val (p,q)/(left π).val p := by
  apply (eq_div_iff hp.ne').mpr
  simpa only [mul_comm] using row_weight π p q
lemma col_val (π : Law (P×Q)) {q : Q} (hq : 0<(right π).val q) (p : P) :
    (col π q).val p=π.val (p,q)/(right π).val q := by
  apply (eq_div_iff hq.ne').mpr
  simpa only [mul_comm] using col_weight π p q
end
end PlanarUnitDistances.FiniteStarCoupling

namespace PlanarUnitDistances.TemplateCoupling
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q Θ : Type*} [Fintype P] [Fintype Q] [Fintype Θ]

def joint (π : Law (P×Q)) (a : Q → Law Θ) : Law ((P×Q)×Θ) := dependent π (fun pq => a pq.2)
def templates (π : Law (P×Q)) (a : Q → Law Θ) : Law Θ := push (joint π a) Prod.snd
def slice (π : Law (P×Q)) (a : Q → Law Θ) (θ : Θ) : Law (P×Q) :=
  push (cond (joint π a) Prod.snd θ) Prod.fst

lemma slice_weight (π : Law (P×Q)) (a : Q → Law Θ) (θ : Θ) (pq : P×Q) :
    (templates π a).val θ*(slice π a θ).val pq=π.val pq*(a pq.2).val θ := by
  exact col_weight (joint π a) pq θ
lemma slice_avg (π : Law (P×Q)) (a : Q → Law Θ) (f : Θ → P×Q → ℝ) :
    avg (templates π a) (fun θ => avg (slice π a θ) (f θ))=
      avg π (fun pq => avg (a pq.2) (fun θ => f θ pq)) := by
  simp only [slice,push_avg]
  change avg (push (joint π a) Prod.snd) _=_
  rw [cond_tower_dep]
  exact dependent_avg π _ _
lemma slice_event (π : Law (P×Q)) (a : Q → Law Θ) (f : Θ → P×Q → Prop) :
    avg (templates π a) (fun θ => event (slice π a θ) (f θ))=
      avg π (fun pq => event (a pq.2) (fun θ => f θ pq)) := by
  unfold event
  exact slice_avg π a _
lemma slice_right_weight (π : Law (P×Q)) (a : Q → Law Θ) (θ : Θ) (q : Q) :
    (templates π a).val θ*(right (slice π a θ)).val q = (right π).val q*(a q).val θ := by
  simp only [right_val,mul_sum,sum_mul,slice_weight]

lemma col_eq (π : Law (P×Q)) (a : Q → Law Θ) (θ : Θ) (q : Q)
    (ht : 0<(templates π a).val θ) (hq : 0<(right (slice π a θ)).val q) :
    col (slice π a θ) q=col π q := by
  have he := slice_right_weight π a θ q
  apply law_ext
  intro p
  apply (mul_right_inj' (mul_ne_zero ht.ne' hq.ne')).mp
  calc
    _ = (templates π a).val θ*(slice π a θ).val (p,q) := by rw [mul_assoc,col_weight]
    _ = π.val (p,q)*(a q).val θ := slice_weight π a θ (p,q)
    _ = ((templates π a).val θ*(right (slice π a θ)).val q)*(col π q).val p := by
      rw [he]
      calc
        _ = ((right π).val q*(col π q).val p)*(a q).val θ := by rw [col_weight]
        _ = _ := by ring

lemma center_statistic (π : Law (P×Q)) (a : Q → Law Θ) (F : Q → Law P → ℝ) :
    avg (templates π a) (fun θ => avg (right (slice π a θ)) (fun q => F q (col (slice π a θ) q)))=
      avg (right π) (fun q => F q (col π q)) := by
  have he (θ : Θ) (q : Q) :
      (templates π a).val θ*((right (slice π a θ)).val q*F q (col (slice π a θ) q))=
        (right π).val q*(a q).val θ*F q (col π q) := by
    rw [← mul_assoc]
    by_cases ht : 0<(templates π a).val θ
    · by_cases hq : 0<(right (slice π a θ)).val q
      · rw [col_eq π a θ q ht hq,slice_right_weight]
      · have hz := le_antisymm (le_of_not_gt hq) ((right (slice π a θ)).nonneg q)
        rw [← slice_right_weight,hz,mul_zero,zero_mul,zero_mul]
    · have hz := le_antisymm (le_of_not_gt ht) ((templates π a).nonneg θ)
      rw [← slice_right_weight,hz,zero_mul,zero_mul,zero_mul]
  simp only [avg,mul_sum,he]
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  rw [← sum_mul,← mul_sum,(a q).total,mul_one]

lemma center_variation (π : Law (P×Q)) (a : Q → Law Θ) (bit : P → Q → Bool) :
    avg (templates π a) (fun θ => VQ (slice π a θ) bit)=VQ π bit :=
  center_statistic π a (fun q ν => StarScore.variation ν (fun p => bit p q))
lemma center_score {A B : Type*} (π : Law (P×Q)) (a : Q → Law Θ)
    (bit : P → Q → Bool) (x : P → A×B) :
    avg (templates π a) (fun θ => DQ (slice π a θ) bit x)=DQ π bit x :=
  center_statistic π a (fun q ν => StarScore.score ν (fun p => bit p q) x)
end
end PlanarUnitDistances.TemplateCoupling

namespace PlanarUnitDistances.CommonTemplate
open Finset FiniteLaw FiniteStarCoupling TemplateCoupling StrictCross CrossSampling CrossStructure
open scoped Classical
noncomputable section
variable {P Q A B Θ : Type*} [Fintype P] [Fintype Q]
  [Fintype A] [Fintype B] [Fintype Θ]

omit [Fintype A] [Fintype B] in
theorem aggregate_score (π : Law (P×Q)) (a : Q → Law Θ) (bit : P → Q → Bool)
    (x : P → A×B) (y : Q → A×B) (Y U : Θ → Finset (A×B))
    (good : Θ → P → Q → Prop) (hs : ∀θ,Shape (Y θ) (U θ))
    (hg : ∀θ p q,good θ p q → x p∈U θ ∧ y q∈Y θ ∧ Consistent (bit p q) (x p) (y q)) :
    (avg (templates π a) (fun θ => VP (slice π a θ) bit)+VQ π bit)/6 -
      16*avg π (fun pq => event (a pq.2) (fun θ => ¬good θ pq.1 pq.2)) ≤
      avg (templates π a) (fun θ => DP (slice π a θ) bit y)+DQ π bit x := by
  have ht := avg_mono (templates π a) (fun θ => slice_score (slice π a θ) bit x y
    (good θ) (Y θ) (U θ) (hs θ) (hg θ))
  have he : avg (templates π a) (fun θ => (VP (slice π a θ) bit+VQ (slice π a θ) bit)/6)=
      (avg (templates π a) (fun θ => VP (slice π a θ) bit)+VQ π bit)/6 := by
    simp only [div_eq_mul_inv,mul_comm _ (6:ℝ)⁻¹,avg_smul,avg_add,center_variation]
  rw [avg_sub,he,avg_smul,avg_add,center_score] at ht
  simp only [bad,slice_event] at ht
  exact ht
end
end PlanarUnitDistances.CommonTemplate
end OAI
