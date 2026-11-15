import PlanarUnitDistances.CrossComparisons
import PlanarUnitDistances.Prediction
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Finite hash features and prediction on measurable levels. Adapted from the
OAI UnitDistances Predictions module to expose the vector-norm history. -/
namespace OAI
namespace PlanarUnitDistances.FiniteLaw
open Finset MeasureTheory
open scoped Classical
noncomputable section
variable {X Y C : Type*} [Fintype X] [Fintype Y] [Fintype C]

def uniform (X : Type*) [Fintype X] [Nonempty X] : Law X where
  val _ := (Fintype.card X : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by simp [Fintype.card_ne_zero]

lemma uniform_avg [Nonempty X] (f : X → ℝ) :
    avg (uniform X) f = (∑ x, f x) / Fintype.card X := by
  simp [avg,uniform,div_eq_mul_inv,mul_comm,sum_mul]

lemma uniform_equiv [Nonempty X] [Nonempty Y] (e : X ≃ Y) (f : Y → ℝ) :
    avg (uniform X) (fun x => f (e x)) = avg (uniform Y) f := by
  rw [uniform_avg,uniform_avg,e.sum_comp,Fintype.card_congr e]

lemma uniform_pair [Nonempty X] [Nonempty Y] (f : X×Y → ℝ) :
    avg (uniform (X×Y)) f = avg (uniform X) (fun x => avg (uniform Y) (fun y => f (x,y))) := by
  simp only [uniform_avg,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul]
  rw [← sum_div,div_div]
  ring

omit [Fintype Y] in
lemma uniform_eval [DecidableEq X] [Nonempty C] (x : X) (f : C → ℝ) :
    avg (uniform (X → C)) (fun h => f (h x)) = avg (uniform C) f := by
  classical
  let e := Equiv.piSplitAt x (fun _ => C)
  have h := uniform_equiv e (fun z => f z.1)
  change avg (uniform (X → C)) (fun h => f (h x)) = _ at h
  rw [h, uniform_pair]
  simp_rw [avg_const]

omit [Fintype Y] in
lemma uniform_eval_two [DecidableEq X] [Nonempty C] (x y : X) (hxy : x ≠ y) (f : C → C → ℝ) :
    avg (uniform (X → C)) (fun h => f (h x) (h y)) =
      avg (uniform C) (fun a => avg (uniform C) (fun b => f a b)) := by
  classical
  let e := Equiv.piSplitAt x (fun _ => C)
  let y' : {z : X // z ≠ x} := ⟨y,hxy.symm⟩
  have h := uniform_equiv e (fun z => f z.1 (z.2 y'))
  change avg (uniform (X → C)) (fun h => f (h x) (h y)) = _ at h
  rw [h,uniform_pair]
  apply avg_congr
  intro a
  exact uniform_eval y' (f a)

omit [Fintype Y] in
lemma uniform_collision [DecidableEq X] [Nonempty C] (x y : X) (hxy : x ≠ y) :
    event (uniform (X → C)) (fun h => h x=h y) = (Fintype.card C : ℝ)⁻¹ := by
  unfold event
  have he := uniform_eval_two x y hxy (fun a b : C => if a=b then 1 else 0)
  rw [he]
  have h : ∀ a : C, avg (uniform C) (fun b => if a=b then 1 else 0) =
      (Fintype.card C : ℝ)⁻¹ := by
    intro a
    simp [uniform_avg]
  simp_rw [h]
  exact avg_const _ _

def Law.pmf (μ : Law X) : PMF X := PMF.ofFintype (fun x => ENNReal.ofReal (μ.val x)) (by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => μ.nonneg x),μ.total,ENNReal.ofReal_one])


lemma integral_pmf [MeasurableSpace X] [MeasurableSingletonClass X] (μ : Law X) (f : X → ℝ) :
    (∫ x,f x ∂μ.pmf.toMeasure) = avg μ f := by
  rw [PMF.integral_eq_sum]
  change ∑ x, (ENNReal.ofReal (μ.val x)).toReal * f x = _
  simp [avg,μ.nonneg]
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.HashFeatures
open Finset Real
open scoped RealInnerProductSpace Classical
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]

abbrev Index (A B : Type*) := A ⊕ (B ⊕ A×B)
abbrev V (A B : Type*) [Fintype A] [Fintype B] := EuclideanSpace ℝ (Index A B)

def vector (x : A×B) (a b c : ℝ) : V A B := by
  classical
  exact WithLp.toLp 2 (Sum.elim (Pi.single x.1 a)
    (Sum.elim (Pi.single x.2 b) (Pi.single x c)))

lemma single_inner {T : Type*} [Fintype T] [DecidableEq T] (x y : T) (a b : ℝ) :
    (∑ i, Pi.single y b i * Pi.single x a i) = if x=y then a*b else 0 := by
  simp only [Pi.single_apply,ite_mul,mul_ite,zero_mul,mul_zero]
  by_cases h : x=y
  · subst y; simp [mul_comm]
  · simp [h]

lemma inner_vector (x y : A×B) (a b c d e f : ℝ) :
    inner ℝ (vector x a b c) (vector y d e f) =
      (if x.1=y.1 then a*d else 0)+(if x.2=y.2 then b*e else 0)+
      (if x=y then c*f else 0) := by
  classical
  rw [PiLp.inner_apply]
  simp only [vector,WithLp.ofLp_toLp,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    RCLike.inner_apply,conj_trivial]
  rw [single_inner,single_inner,single_inner]
  ring

lemma norm_vector_sq (x : A×B) (a b c : ℝ) : ‖vector x a b c‖^2 = a^2+b^2+c^2 := by
  rw [← real_inner_self_eq_norm_sq,inner_vector]
  simp only [ite_true]
  ring

lemma norm_feature (x : A×B) : ‖vector x 1 1 1‖=sqrt 3 := by
  have h := norm_vector_sq x 1 1 1
  have hs := sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  nlinarith [norm_nonneg (vector x 1 1 1),sqrt_nonneg 3]
lemma norm_test (x : A×B) : ‖vector x 1 1 (-2)‖=sqrt 6 := by
  have h := norm_vector_sq x 1 1 (-2)
  have hs := sq_sqrt (by norm_num : (0:ℝ) ≤ 6)
  nlinarith [norm_nonneg (vector x 1 1 (-2)),sqrt_nonneg 6]

lemma strict_cross_inner (x y : A×B) :
    inner ℝ (vector x 1 1 1) (vector y 1 1 (-2)) =
      if (x.1=y.1 ∧ x.2≠y.2) ∨ (x.1≠y.1 ∧ x.2=y.2) then 1 else 0 := by
  classical
  rw [inner_vector]
  by_cases h₁ : x.1=y.1 <;> by_cases h₂ : x.2=y.2
  · have he : x=y := Prod.ext h₁ h₂
    subst y
    norm_num
  · have hn : x≠y := fun h => h₂ (congrArg Prod.snd h)
    simp [h₁,h₂,hn]
  · have hn : x≠y := fun h => h₁ (congrArg Prod.fst h)
    simp [h₁,h₂,hn]
  · have hn : x≠y := fun h => h₁ (congrArg Prod.fst h)
    simp [h₁,h₂,hn]

end
end PlanarUnitDistances.HashFeatures

namespace PlanarUnitDistances.FiniteLaw
open Finset
noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]
lemma avg_comm (μ : Law X) (ν : Law Y) (f : X → Y → ℝ) :
    avg μ (fun x => avg ν (f x)) = avg ν (fun y => avg μ (fun x => f x y)) := by
  simp only [avg,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro x _
  ring
lemma abs_avg_le (μ : Law X) (f : X → ℝ) : |avg μ f| ≤ avg μ (fun x => |f x|) := by
  calc
    _ ≤ ∑ x,|μ.val x*f x| := abs_sum_le_sum_abs _ _
    _ = _ := by simp [avg,abs_mul,abs_of_nonneg,μ.nonneg]
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.Hashing
open Finset FiniteLaw StrictCross
open scoped Classical
noncomputable section
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [Nonempty C]

abbrev Hash (A B C : Type*) := (A → C) × (B → C)
def law : Law (Hash A B C) := pair (uniform (A → C)) (uniform (B → C))
def state (h : Hash A B C) (x : A×B) : C×C := (h.1 x.1,h.2 x.2)

def indicator (x y : A×B) : ℝ := if Adj x y then 1 else 0

omit [Fintype A] [Fintype B] [Fintype C] [Nonempty C] in
lemma error_pointwise (h : Hash A B C) (x y : A×B) :
    |indicator (state h x) (state h y) - indicator x y| ≤
      (if x.1≠y.1 ∧ h.1 x.1=h.1 y.1 then 1 else 0) +
      (if x.2≠y.2 ∧ h.2 x.2=h.2 y.2 then 1 else 0) := by
  unfold indicator Adj state
  dsimp only
  by_cases h₁ : x.1=y.1 <;> by_cases h₂ : x.2=y.2 <;>
    by_cases k₁ : h.1 x.1=h.1 y.1 <;> by_cases k₂ : h.2 x.2=h.2 y.2 <;>
      simp_all

lemma coord_error {D : Type*} [Fintype D] [DecidableEq D] (x y : D) :
    avg (uniform (D → C)) (fun h => if x≠y ∧ h x=h y then 1 else 0) ≤
      (Fintype.card C : ℝ)⁻¹ := by
  by_cases hxy : x=y
  · simp only [hxy,ne_eq,not_true_eq_false,false_and,ite_false,avg_const]
    positivity
  · simp only [hxy,ne_eq,not_false_eq_true,true_and]
    rw [avg_ite,uniform_collision x y hxy]

lemma error_bound (x y : A×B) :
    avg (law : Law (Hash A B C)) (fun h => |indicator (state h x) (state h y)-indicator x y|)
      ≤ 2/(Fintype.card C : ℝ) := by
  refine (avg_mono law (fun h => error_pointwise h x y)).trans ?_
  rw [avg_add]
  change avg (pair (uniform (A → C)) (uniform (B → C))) (fun h => if x.1≠y.1 ∧ h.1 x.1=h.1 y.1 then 1 else 0) +
    avg (pair (uniform (A → C)) (uniform (B → C))) (fun h => if x.2≠y.2 ∧ h.2 x.2=h.2 y.2 then 1 else 0) ≤ _
  rw [pair_fst (uniform (A → C)) (uniform (B → C))
    (fun h : A → C => if x.1≠y.1 ∧ h x.1=h y.1 then 1 else 0),
    pair_snd (uniform (A → C)) (uniform (B → C))
    (fun h : B → C => if x.2≠y.2 ∧ h x.2=h y.2 then 1 else 0)]
  have h₁ := coord_error (C := C) x.1 y.1
  have h₂ := coord_error (C := C) x.2 y.2
  linarith [show 2/(Fintype.card C : ℝ) = (Fintype.card C : ℝ)⁻¹+
      (Fintype.card C : ℝ)⁻¹ by ring]

lemma averaged_error (x y : A×B) :
    |avg (law : Law (Hash A B C)) (fun h => indicator (state h x) (state h y))-indicator x y|
      ≤ 2/(Fintype.card C : ℝ) := by
  rw [← avg_const (law : Law (Hash A B C)) (indicator x y),← avg_sub]
  exact (abs_avg_le law _).trans (error_bound x y)
end
end PlanarUnitDistances.Hashing

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

def mixture (μ : Law X) (ν : X → Law Y) : Law Y where
  val y := avg μ (fun x => (ν x).val y)
  nonneg y := avg_nonneg μ (fun x => (ν x).nonneg y)
  total := by
    simp only [avg]
    rw [sum_comm]
    simp_rw [← mul_sum,Law.total,mul_one]
    exact μ.total


lemma abs_avg_sub_le (μ : Law X) {f g : X → ℝ} {c : ℝ} (h : ∀ x,|f x-g x| ≤ c) :
    |avg μ f-avg μ g| ≤ c := by
  rw [← avg_sub]
  exact (abs_avg_le μ _).trans (avg_le_const μ h)
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.CrossPrediction
open Finset FiniteLaw
open scoped Classical
noncomputable section
variable {P Q H A B C T : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Fintype A] [Fintype B] [Fintype C] [Fintype T]
  [DecidableEq H] [DecidableEq A] [DecidableEq B] [Nonempty C]

omit [Fintype H] in
lemma push_mass (μ : Law P) (h : P → H) (a : H) :
    FiniteInformation.push μ.val h a = fiberMass μ h a := by
  rw [fiberMass_eq]
  unfold FiniteInformation.push
  apply sum_congr rfl
  intro x _
  split_ifs <;> rfl

omit [Fintype H] in
lemma posterior_cond (μ : Law P) (h : P → H) (p : P) (hp : 0 < μ.val p) (r : P) :
    FiniteInformation.posterior μ.val h (h p) r = (cond μ h (h p)).val r := by
  have hm : 0 < fiberMass μ h (h p) := hp.trans_le (atom_le_fiber μ h p)
  simp only [FiniteInformation.posterior,push_mass,FiniteLaw.cond,hm,↓reduceDIte]
  split_ifs <;> simp

def actual (κ : Law Q) (w : Q → Law P) (X : P → A×B) (Z : Q → A×B) : ℝ :=
  avg κ (fun q => avg (w q) (fun p => Hashing.indicator (X p) (Z q)))

def predicted (κ : Law Q) (w : Q → Law P) (h : P → H) (X : P → A×B) (Z : Q → A×B) : ℝ :=
  avg κ (fun q => avg (w q) (fun p =>
    avg (cond (mixture κ w) h (h p)) (fun r => Hashing.indicator (X r) (Z q))))

lemma actual_hash_error (κ : Law Q) (w : Q → Law P) (X : P → A×B) (Z : Q → A×B) :
    |avg (Hashing.law : Law (Hashing.Hash A B C))
      (fun u => actual κ w (Hashing.state u ∘ X) (Hashing.state u ∘ Z))-actual κ w X Z|
      ≤ 2/(Fintype.card C : ℝ) := by
  unfold actual
  rw [avg_comm]
  simp_rw [avg_comm (Hashing.law : Law (Hashing.Hash A B C))]
  apply abs_avg_sub_le
  intro q
  apply abs_avg_sub_le
  intro p
  exact Hashing.averaged_error (X p) (Z q)

omit [Fintype H] [DecidableEq H] in
lemma predicted_hash_error (κ : Law Q) (w : Q → Law P) (h : P → H)
    (X : P → A×B) (Z : Q → A×B) :
    |avg (Hashing.law : Law (Hashing.Hash A B C))
      (fun u => predicted κ w h (Hashing.state u ∘ X) (Hashing.state u ∘ Z))-
          predicted κ w h X Z| ≤ 2/(Fintype.card C : ℝ) := by
  unfold predicted
  rw [avg_comm]
  simp_rw [avg_comm (Hashing.law : Law (Hashing.Hash A B C))]
  apply abs_avg_sub_le
  intro q
  apply abs_avg_sub_le
  intro p
  apply abs_avg_sub_le
  intro r
  exact Hashing.averaged_error (X r) (Z q)

lemma discrepancy_eq (κ : Law Q) (w : Q → Law P) (h : P → H)
    (hμ : ∀ p,0 < (mixture κ w).val p) (X : P → A×B) (Z : Q → A×B) :
    FiniteInformation.testDiscrepancy κ.val (fun q => (w q).val) h X
      (fun x => HashFeatures.vector x 1 1 1) (fun q => HashFeatures.vector (Z q) 1 1 (-2)) =
      |actual κ w X Z-predicted κ w h X Z| := by
  have hm : FiniteInformation.marginal κ.val (fun q => (w q).val) = (mixture κ w).val := rfl
  have hi : ∀ x y : A×B, inner ℝ (HashFeatures.vector x 1 1 1)
      (HashFeatures.vector y 1 1 (-2)) = Hashing.indicator x y := by
    intro x y
    rw [HashFeatures.strict_cross_inner]
    unfold Hashing.indicator StrictCross.Adj
    split_ifs <;> rfl
  unfold FiniteInformation.testDiscrepancy
  rw [hm]
  simp_rw [FiniteInformation.mean_posterior,posterior_cond _ _ _ (hμ _),sum_inner,
    real_inner_smul_left,inner_sub_left,sum_inner,real_inner_smul_left,
    hi]
  simp only [actual,predicted,avg]
  congr 1
  simp only [mul_sub,sum_sub_distrib]
omit [Fintype H] [DecidableEq H] in
lemma hash_transfer (κ : Law Q) (w : Q → Law P) (h : P → H)
    (X : P → A×B) (Z : Q → A×B) :
    actual κ w X Z-predicted κ w h X Z ≤
      avg (Hashing.law : Law (Hashing.Hash A B C)) (fun u =>
        |actual κ w (Hashing.state u ∘ X) (Hashing.state u ∘ Z)-
          predicted κ w h (Hashing.state u ∘ X) (Hashing.state u ∘ Z)|)+
        4/(Fintype.card C : ℝ) := by
  have ha := actual_hash_error (C := C) κ w X Z
  have hp := predicted_hash_error (C := C) κ w h X Z
  have he := avg_mono (Hashing.law : Law (Hashing.Hash A B C)) (fun u =>
    le_abs_self (actual κ w (Hashing.state u ∘ X) (Hashing.state u ∘ Z)-
      predicted κ w h (Hashing.state u ∘ X) (Hashing.state u ∘ Z)))
  rw [avg_sub] at he
  have ha' := (abs_le.mp ha).1
  have hp' := (abs_le.mp hp).2
  simp only [div_eq_mul_inv] at ha' hp' ⊢
  linarith

open MeasureTheory Real
lemma hash_history_singletons (D : Type*) [MeasurableSpace D] [MeasurableSingletonClass D] (n : ℕ) :
    MeasurableSingletonClass (FiniteInformation.History D n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSingletonClass PUnit)
  | succ n ih =>
    let := ih
    exact inferInstanceAs (MeasurableSingletonClass (FiniteInformation.History D n × D))

def hashNorm (κ : Law Q) (w : Q → Law P) (h : P → H) (X : P → A×B) : ℝ :=
  avg (Hashing.law : Law (Hashing.Hash A B C)) (fun u =>
    FiniteInformation.predictionNorm κ.val (fun q => (w q).val) h
      (Hashing.state u ∘ X) (fun c => HashFeatures.vector c 1 1 1))

theorem exists_vector_cross_history (κ : Law Q) (w : Q → Law P) (τ : Law T)
    (X : T → P → A×B) (K : ℕ) (hK : 0 < K) :
    ∃ n < K, ∃ h : P → FiniteInformation.History (C×C) n,
      (univ.image h).card ≤ (Fintype.card C)^(2*(K-1)) ∧
      avg τ (fun t => hashNorm (C := C) κ w h (X t)) ≤
        4*sqrt 3*(FiniteInformation.KL (FiniteInformation.wedge κ.val (fun q => (w q).val))
         (fun pr : P×P => (mixture κ w).val pr.1 * (mixture κ w).val pr.2)/(K:ℝ))^(1/4:ℝ) := by
  classical
  let : MeasurableSpace (C×C) := ⊤
  let : MeasurableSpace (T × Hashing.Hash A B C) := ⊤
  let σ := pair τ (Hashing.law : Law (Hashing.Hash A B C))
  let code := fun tu : T × Hashing.Hash A B C => Hashing.state tu.2 ∘ X tu.1
  let feature := fun _ : T × Hashing.Hash A B C => fun c : C×C => HashFeatures.vector c 1 1 1
  have meas : ∀ n, Measurable (fun z : (P → FiniteInformation.History (C×C) n) × (T × Hashing.Hash A B C) =>
      FiniteInformation.predictionNorm κ.val (fun q => (w q).val) z.1 (code z.2) (feature z.2)) := by
    intro n
    let := hash_history_singletons (C×C) n
    exact measurable_of_finite _
  obtain ⟨n,hn,past,sb,bd⟩ := FiniteInformation.exists_vector_prediction_history (ν := σ.pmf.toMeasure)
    κ.val (fun q => (w q).val) κ.nonneg (fun q => (w q).nonneg) κ.total (fun q => (w q).total)
    code feature (fun _ => measurable_of_finite _) meas (sqrt_nonneg 3) (fun _ c => (HashFeatures.norm_feature c).le) K hK
  refine ⟨n,hn,FiniteInformation.transcript (fun j => code (past j)) n,?_,?_⟩
  · simpa only [Fintype.card_prod,← pow_two,← pow_mul] using sb
  · rw [integral_pmf,pair_avg] at bd
    exact bd

theorem discrepancy_norm_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {D : Type*} [Fintype D] [DecidableEq D] (κ : Law Q) (w : Q → Law P)
    (h : P → H) (c : P → D) (v : D → V) (g : Q → V) {M : ℝ}
    (hg : ∀ q, ‖g q‖ ≤ M) :
    FiniteInformation.testDiscrepancy κ.val (fun q => (w q).val) h c v g ≤
      M * FiniteInformation.predictionNorm κ.val (fun q => (w q).val) h c v := by
  let f := FiniteInformation.conditionalResidual κ.val (fun q => (w q).val) h c v
  change |∑ q, κ.val q * inner ℝ (f q) (g q)| ≤ M * ∑ q, κ.val q * ‖f q‖
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro q _
  rw [abs_mul,abs_of_nonneg (κ.nonneg q),mul_left_comm,mul_comm M]
  apply mul_le_mul_of_nonneg_left _ (κ.nonneg q)
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hg q) (norm_nonneg _))

theorem cross_error_same_history (κ : Law Q) (w : Q → Law P)
    (hμ : ∀ p,0 < (mixture κ w).val p) (h : P → H) (X : P → A×B) (Z : Q → A×B) :
    actual κ w X Z-predicted κ w h X Z ≤ 4/(Fintype.card C:ℝ)+sqrt 6*hashNorm (C := C) κ w h X := by
  have he := hash_transfer (C := C) κ w h X Z
  rw [add_comm]
  apply he.trans (add_le_add_left ?_ _)
  rw [hashNorm,← avg_smul]
  apply avg_mono
  intro u
  rw [← discrepancy_eq κ w h hμ]
  exact discrepancy_norm_bound κ w h _ _ _ (fun q => (HashFeatures.norm_test _).le)

end
end PlanarUnitDistances.CrossPrediction

namespace PlanarUnitDistances.FiniteLaw
open MeasureTheory Finset Set
open scoped Classical
noncomputable section
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
lemma sum_real_atoms (μ : Measure S) [IsFiniteMeasure μ] : ∑s,μ.real {s}=μ.real Set.univ := by
  have hi := integral_fintype (f := fun _ : S => (1:ℝ)) (μ := μ) (integrable_const 1)
  simpa only [integral_const,smul_eq_mul,mul_one] using hi.symm

def fromMeasure (μ : Measure S) [IsFiniteMeasure μ] (hμ : 0<μ.real Set.univ) : Law S where
  val s := μ.real {s}/μ.real Set.univ
  nonneg s := div_nonneg ENNReal.toReal_nonneg hμ.le
  total := by rw [←sum_div,sum_real_atoms,div_self hμ.ne']

lemma fromMeasure_avg (μ : Measure S) [IsFiniteMeasure μ] (hμ : 0<μ.real Set.univ) (f : S → ℝ) :
    avg (fromMeasure μ hμ) f=(∫s,f s ∂μ)/μ.real Set.univ := by
  rw [integral_fintype (Integrable.of_finite)]
  simp only [avg,fromMeasure,smul_eq_mul]
  rw [Finset.sum_div]
  apply sum_congr rfl; intro s _; ring

variable {Ω : Type*} [MeasurableSpace Ω]
omit [Fintype S] [MeasurableSingletonClass S] in
lemma map_real_univ (μ : Measure Ω) (c : Ω → S) (hc : Measurable c) :
    (μ.map c).real Set.univ=μ.real Set.univ := by
  simp only [Measure.real,Measure.map_apply hc MeasurableSet.univ,Set.preimage_univ]

def compress (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : 0<μ.real Set.univ)
    (c : Ω → S) (hc : Measurable c) : Law S :=
  fromMeasure (μ.map c) (by rwa [map_real_univ μ c hc])

lemma compress_avg (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : 0<μ.real Set.univ)
    (c : Ω → S) (hc : Measurable c) (f : S → ℝ) :
    avg (compress μ hμ c hc) f=(∫s,f (c s) ∂μ)/μ.real Set.univ := by
  rw [compress,fromMeasure_avg,map_real_univ μ c hc,
    integral_map hc.aemeasurable (measurable_of_finite f).aestronglyMeasurable]
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.CrossPrediction
open Finset FiniteLaw MeasureTheory
open scoped Classical
noncomputable section
variable {P Q A B C Ω : Type*} [Fintype P] [Fintype Q] [Fintype A] [Fintype B]
  [Fintype C] [Nonempty C] [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [MeasurableSingletonClass B] [MeasurableSpace Ω]


end
end PlanarUnitDistances.CrossPrediction

end OAI
