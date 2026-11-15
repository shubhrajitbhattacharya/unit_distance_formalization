import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The exact exponent from Theorem A and the numerical
estimates used at the transition between the small- and large-height arguments. -/

noncomputable section

namespace PlanarUnitDistances

def H0 : ℝ := 226 * (2 ^ 2100 + 1)

def N0 : ℕ := ⌈32 * Real.exp (19 * H0)⌉₊

def exactGap : ℝ := 1 / (30600 * (7200 * (N0 : ℝ)) ^ 4 * Real.log (1 + (N0 : ℝ) ^ 4))


private theorem H0_large : (1000000 : ℝ) ≤ H0 := by
  have h : (2 : ℝ) ^ 13 ≤ 2 ^ 2100 := pow_le_pow_right₀ (by norm_num) (by decide)
  norm_num only [show (2 : ℝ) ^ 13 = 8192 by norm_num] at h
  unfold H0
  exact (show ∀ x : ℝ, 8192 ≤ x → 1000000 ≤ 226 * (x + 1) by
    intro x hx; linarith) _ h

private theorem N0_bounds : 32 * Real.exp (19 * H0) ≤ (N0 : ℝ) ∧
    (N0 : ℝ) ≤ 33 * Real.exp (19 * H0) := by
  have he : 1 ≤ Real.exp (19 * H0) := Real.one_le_exp (by linarith [H0_large])
  exact ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one (by positivity :
    0 ≤ 32 * Real.exp (19 * H0))).le.trans (by linarith)⟩

private theorem N0_large : (32 : ℝ) ≤ (N0 : ℝ) := by
  have he : 1 ≤ Real.exp (19 * H0) := Real.one_le_exp (by linarith [H0_large])
  linarith [N0_bounds.1]

private theorem logM_gt_one : 1 < Real.log (1 + (N0 : ℝ) ^ 4) := by
  have hpow : (32 : ℝ) ^ 4 ≤ (N0 : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) N0_large _
  have h : (2 : ℝ) ^ 2 ≤ 1 + (N0 : ℝ) ^ 4 := by linarith
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ 2) h
  rw [Real.log_pow] at hl
  norm_num at hl
  linarith [Real.log_two_gt_d9]

theorem exactGap_pos : 0 < exactGap := by
  have hN : 0 < (N0 : ℝ) := by linarith [N0_large]
  have hM : 0 < Real.log (1 + (N0 : ℝ) ^ 4) := by linarith [logM_gt_one]
  unfold exactGap
  positivity


private theorem neg_log_exactGap_eq :
    -Real.log exactGap = Real.log 30600 + 4 * (Real.log 7200 + Real.log (N0 : ℝ)) +
      Real.log (Real.log (1 + (N0 : ℝ) ^ 4)) := by
  have hN : 0 < (N0 : ℝ) := by linarith [N0_large]
  have hM : 0 < Real.log (1 + (N0 : ℝ) ^ 4) := by linarith [logM_gt_one]
  rw [exactGap, one_div, Real.log_inv, neg_neg, Real.log_mul (by positivity) hM.ne',
    Real.log_mul (by norm_num) (by positivity), Real.log_pow,
    Real.log_mul (by norm_num) hN.ne']
  norm_num

/-- The strict logarithmic bounds used in the manuscript, before rounding. -/
theorem exactGap_log_bounds :
    76 * H0 < -Real.log exactGap ∧ -Real.log exactGap < 77 * H0 + Real.log 30600 := by
  have hN : 0 < (N0 : ℝ) := by linarith [N0_large]
  have hH : 0 < H0 := by linarith [H0_large]
  have hNlower := Real.log_le_log (by positivity) N0_bounds.1
  have hNupper := Real.log_le_log hN N0_bounds.2
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at hNlower hNupper
  have hlogN : Real.log (N0 : ℝ) ≤ 19 * H0 + 32 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 33)]
  have hpow : 1 ≤ (N0 : ℝ) ^ 4 := one_le_pow₀ (by linarith [N0_large])
  have hLM := Real.log_le_log (by positivity : 0 < 1 + (N0 : ℝ) ^ 4)
    (show 1 + (N0 : ℝ) ^ 4 ≤ 2 * (N0 : ℝ) ^ 4 by linarith)
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hLM
  have hMupper : Real.log (1 + (N0 : ℝ) ^ 4) ≤ 100 * H0 := by
    norm_num only [Nat.cast_ofNat] at hLM
    linarith [H0_large, Real.log_two_lt_d9]
  have hloglog := Real.log_le_log (by linarith [logM_gt_one]) hMupper
  rw [Real.log_mul (by norm_num) hH.ne'] at hloglog
  have hlogH : Real.log H0 ≤ H0 / 2 + 1 := by
    have heq : H0 = 2 * (H0 / 2) := by ring
    calc
      Real.log H0 = Real.log 2 + Real.log (H0 / 2) := by
        rw [← Real.log_mul (by norm_num) (by positivity : H0 / 2 ≠ 0), ← heq]
      _ ≤ H0 / 2 + 1 := by
        linarith [Real.log_two_lt_d9, Real.log_le_sub_one_of_pos (by positivity : 0 < H0 / 2)]
  rw [neg_log_exactGap_eq]
  constructor
  · linarith [Real.log_pos (by norm_num : (1 : ℝ) < 32),
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 7200),
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 30600), Real.log_nonneg logM_gt_one.le]
  · linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 100),
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 7200), H0_large]


/-- The same exact saving fits the large-height argument's separate parameter range. -/
theorem exactGap_lt_largeHeightGap : exactGap < (2 : ℝ) ^ (-(594036 : ℝ)) := by
  apply (Real.log_lt_log_iff exactGap_pos (Real.rpow_pos_of_pos (by norm_num) _)).mp
  rw [Real.log_rpow (by norm_num)]
  linarith [exactGap_log_bounds.1, H0_large, Real.log_two_lt_d9]

theorem exactGap_normalization :
    30600 * exactGap * (7200 * (N0 : ℝ)) ^ 4 * Real.log (1 + (N0 : ℝ) ^ 4) = 1 := by
  have hN : 0 < (N0 : ℝ) := by linarith [N0_large]
  have hM : 0 < Real.log (1 + (N0 : ℝ) ^ 4) := by linarith [logM_gt_one]
  unfold exactGap
  field_simp

/-- Endpoint in equation (K−1) log M < log t. The natural ceiling models the
number of samples; subtracting one after casting keeps the strict inequality. -/
theorem smallHeight_history_log_lt {D t : ℝ} (hD : 0 ≤ D)
    (hMI : D + 1 ≤ 30600 * exactGap * Real.log t) :
    let A := (7200 * (N0 : ℝ)) ^ 4
    let M := 1 + (N0 : ℝ) ^ 4
    let K := ⌈A * (D + 1)⌉₊
    ((K : ℝ) - 1) * Real.log M < Real.log t := by
  dsimp only
  let A : ℝ := (7200 * (N0 : ℝ)) ^ 4
  let M : ℝ := 1 + (N0 : ℝ) ^ 4
  have hN : 0 < (N0 : ℝ) := by linarith [N0_large]
  have hA : 0 < A := by dsimp [A]; positivity
  have hM : 0 < Real.log M := by dsimp [M]; linarith [logM_gt_one]
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ A * (D + 1) by positivity)
  change ((⌈A * (D + 1)⌉₊ : ℝ) - 1) * Real.log M < Real.log t
  calc
    _ < A * (D + 1) * Real.log M := by gcongr; linarith
    _ ≤ A * (30600 * exactGap * Real.log t) * Real.log M := by gcongr
    _ = (30600 * exactGap * A * Real.log M) * Real.log t := by ring
    _ = Real.log t := by rw [show 30600 * exactGap * A * Real.log M = 1
      from exactGap_normalization, one_mul]

/-- The final graph density exponent comparison holds for the full range
0 < δ ≤ 2^(-594036), including Theorem A and the number-field version. -/
theorem graph_density_exponent {δ : ℝ} (hδ : δ ≤ (2 : ℝ) ^ (-(594036 : ℝ))) :
    let g := 3 * δ
    let a := 10000 * g
    (2 - 1 / 100000) * (1 + 2 * a) < 2 + 3 * a - 180 * g := by
  have hpower : (2 : ℝ) ^ (-(594036 : ℝ)) ≤ (2 : ℝ) ^ (-(32 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    norm_num
  have h32 : (2 : ℝ) ^ (-(32 : ℝ)) = 1 / 4294967296 := by
    rw [Real.rpow_neg (by norm_num), ← Nat.cast_ofNat (R := ℝ) (n := 32),
      Real.rpow_natCast]
    norm_num
  rw [h32] at hpower
  dsimp only
  linarith

/-- After the two comparisons have been added, the error coefficient still
leaves more than S/203 in the point exceptional widths. -/
theorem exceptional_width_gt {S X Y : ℝ} (hS : 0 < S)
    (h₁ : S ≤ X + 201 * Y + 30721 * ((2 : ℝ) ^ 144)⁻¹ * S)
    (h₂ : Y ≤ X + 2048 * ((2 : ℝ) ^ 144)⁻¹ * S) : S / 203 < X := by
  have he : 442369 * ((2 : ℝ) ^ 144)⁻¹ < 1 / 203 := by norm_num
  have h := mul_lt_mul_of_pos_right he hS
  linarith

end PlanarUnitDistances
