import PlanarUnitDistances.Information
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open Finset Real MeasureTheory
open scoped RealInnerProductSpace Classical BigOperators

namespace PlanarUnitDistances.BoundedHeight
open OAI.PlanarUnitDistances.FiniteInformation
noncomputable section

def codeVector {C : Type*} [Fintype C] [DecidableEq C] (c : C) : EuclideanSpace ℝ (Option C) :=
  WithLp.toLp 2 (fun i => if i = none ∨ i = some c then 1 else 0)

def testVector {C : Type*} [Fintype C] [DecidableEq C] (overflow : Prop) (A : Finset C) :
    EuclideanSpace ℝ (Option C) :=
  WithLp.toLp 2 (fun i => match i with
    | none => if overflow then 1 else 0
    | some c => if ¬overflow ∧ c ∈ A then 1 else 0)

theorem membership_inner {C : Type*} [Fintype C] [DecidableEq C]
    (c : C) (o : Prop) (A : Finset C) :
    inner ℝ (codeVector c) (testVector o A) = if o ∨ c ∈ A then 1 else 0 := by
  classical
  rw [PiLp.inner_apply]
  simp only [codeVector, testVector, WithLp.ofLp_toLp, Fintype.sum_option, RCLike.inner_apply,
    conj_trivial, Option.some_ne_none, false_or, Option.some.injEq, true_or, if_true, mul_one]
  by_cases ho : o <;> by_cases hc : c ∈ A <;> simp [ho,hc,mul_ite]

theorem codeVector_norm {C : Type*} [Fintype C] [DecidableEq C] (c : C) :
    ‖codeVector c‖ ≤ sqrt 2 := by
  have n : ‖codeVector c‖^2 = 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp [codeVector]
    have he : Finset.univ.filter (fun x : Option C => x = none ∨ x = some c) = {none, some c} := by
      ext i; simp
    rw [he]; simp
  nlinarith [norm_nonneg (codeVector c), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
    Real.sqrt_nonneg (2:ℝ)]

theorem testVector_norm {C : Type*} [Fintype C] [DecidableEq C] (o : Prop) (A : Finset C)
    {N : ℕ} (hN : 0 < N) (hcard : A.card ≤ 32*N^2+1) :
    ‖testVector o A‖ ≤ 9*(N:ℝ)/Real.sqrt 2 := by
  have hf : ‖testVector o A‖^2 = if o then 1 else (A.card : ℝ) := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    by_cases he : o <;> simp [testVector,Fintype.sum_option, he]
  have n1 : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  have card : (A.card : ℝ) ≤ 32*(N:ℝ)^2+1 := by exact_mod_cast hcard
  apply (le_div_iff₀ (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2))).2
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, hf, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  split_ifs <;> nlinarith [sq_nonneg ((N:ℝ)-1)]

private lemma history_singleton (C : Type*) [MeasurableSpace C] [MeasurableSingletonClass C] (n : ℕ) :
    MeasurableSingletonClass (History C n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSingletonClass PUnit)
  | succ n ih =>
    let := ih
    exact inferInstanceAs (MeasurableSingletonClass (History C n × C))

/-- Uniform tests on finite sets, with an explicit sparse set of accepted code
states and one overflow flag per center and test. The single history is chosen
for the supplied circle membership test. The predicted acceptance is averaged
over the true center, its true neighbor, and the latter's history resampling. -/
theorem exists_sparse_test_history {P Q T C : Type*} [Fintype P] [Fintype Q] [Fintype T]
    [Nonempty T] [Fintype C] [Nonempty C] [DecidableEq C]
    (κ : Q → ℝ) (w : Q → P → ℝ) (hk : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p)
    (hsκ : ∑ q, κ q = 1) (hsw : ∀ q, ∑ p, w q p = 1)
    (code : T → P → C) (flag : T → Q → Prop) (A : T → Q → Finset C) (N K : ℕ)
    (hN : 0 < N) (hK : 0 < K) (hcard : ∀ t q, (A t q).card ≤ 32*N^2+1)
    (htrue : ∀ t q p, w q p ≠ 0 → flag t q ∨ code t p ∈ A t q) :
    ∃ n < K, ∃ hist : P → History C n, (Finset.univ.image hist).card ≤ (Fintype.card C)^(K-1) ∧
      1 - (∑ t, ∑ q, κ q * ∑ p, w q p * ∑ r,
          posterior (marginal κ w) hist (hist p) r *
          (if flag t q ∨ code t r ∈ A t q then 1 else 0)) / Fintype.card T ≤
        36*N*(KL (wedge κ w) (fun pr : P×P => marginal κ w pr.1*marginal κ w pr.2)/(K:ℝ))^(1/4:ℝ) := by
  classical
  letI : MeasurableSpace T := ⊤
  letI : MeasurableSpace C := ⊤
  letI : MeasurableSingletonClass T := ⟨fun _ => trivial⟩
  letI : MeasurableSingletonClass C := ⟨fun _ => trivial⟩
  let ν := Measure.uniformOfFinset (Finset.univ : Finset T)
  haveI : IsProbabilityMeasure ν := ⟨by
    dsimp only [ν]
    rw [Measure.uniformOfFinset_apply]
    simp
    exact ENNReal.div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (by finiteness)⟩
  let v := fun (_ : T) (c : C) => codeVector c
  let g := fun (t : T) q => testVector (flag t q) (A t q)
  have meas (n : ℕ) : Measurable (fun z : (P → History C n) × T =>
      testDiscrepancy κ w z.1 (code z.2) (v z.2) (g z.2)) := by
    letI := history_singleton C n
    exact measurable_of_finite _
  obtain ⟨n,hn,h,hh,bd⟩ := exists_prediction_history (ν := ν) κ w hk hw hsκ hsw code v g
    (fun p => measurable_of_finite _) meas (Real.sqrt_nonneg 2) (by positivity : 0 ≤ 9*(N:ℝ)/Real.sqrt 2)
    (fun t c => codeVector_norm c) (fun t q => testVector_norm _ _ hN (hcard t q)) K hK
  refine ⟨n,hn,h,hh,?_⟩
  let pred (t : T) := ∑ q, κ q * ∑ p, w q p * ∑ r, posterior (marginal κ w) h (h p) r *
    (if flag t q ∨ code t r ∈ A t q then 1 else 0)
  have testEq (t : T) : testDiscrepancy κ w h (code t) (v t) (g t) = |1-pred t| := by
    unfold testDiscrepancy
    simp_rw [mean_posterior, sum_inner, real_inner_smul_left, inner_sub_left, sum_inner, real_inner_smul_left]
    dsimp [v,g,pred]
    simp_rw [membership_inner, mul_sub, Finset.sum_sub_distrib]
    have trueSum (q : Q) :
        (∑ p, w q p * (if flag t q ∨ code t p ∈ A t q then 1 else 0)) = 1 := by
      apply Eq.trans _ (hsw q)
      apply Finset.sum_congr rfl
      intro p _
      by_cases h₀ : w q p = 0 <;> simp [h₀, htrue t q p]
    simp only [trueSum, mul_sub, mul_one, Finset.sum_sub_distrib, hsκ]
  rw [integral_fintype Integrable.of_finite] at bd
  simp only [ν,measureReal_def,Measure.uniformOfFinset_apply_singleton,Finset.mem_univ,ite_true,
    Finset.card_univ,ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul,
    testEq, ← Finset.mul_sum] at bd
  have absBd := Finset.sum_le_sum (s := Finset.univ) (fun t _ => le_abs_self (1-pred t))
  have dv := div_le_div_of_nonneg_right absBd (Nat.cast_nonneg (Fintype.card T) : 0 ≤ (Fintype.card T:ℝ))
  have hcardT : (Fintype.card T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have lhs : (∑ t, (1-pred t)) / (Fintype.card T : ℝ) = 1 - (∑ t, pred t)/(Fintype.card T:ℝ) := by
    rw [Finset.sum_sub_distrib, sub_div]; simp [hcardT]
  have rhs : 4*Real.sqrt 2*(9*(N:ℝ)/Real.sqrt 2) = 36*N := by
    field_simp
    ring
  rw [rhs] at bd
  change 1 - (∑ t, pred t)/(Fintype.card T:ℝ) ≤ _
  rw [← lhs]
  exact dv.trans (by simpa only [div_eq_inv_mul] using bd)

end
end PlanarUnitDistances.BoundedHeight

