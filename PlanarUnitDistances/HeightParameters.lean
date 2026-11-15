import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import PlanarUnitDistances.CircleCells

namespace PlanarUnitDistances.BoundedHeight
open Real
noncomputable section

def gridSize (H : ℝ) : ℕ := ⌈32*exp (19*H)⌉₊
def sampleSize (N : ℕ) (D : ℝ) : ℕ := ⌈(7200*(N:ℝ))^4*(D+1)⌉₊

theorem grid_positive (H : ℝ) : 0 < gridSize H := Nat.ceil_pos.mpr (by positivity)

theorem grid_mesh (H : ℝ) : 8*exp (6*H)*CircleCells.width (exp (6*H)) (gridSize H) ≤ exp (-(7*H)) := by
  have lower : 32*exp (19*H) ≤ (gridSize H : ℝ) := Nat.le_ceil _
  have eqv : exp (-(7*H)) * (32*exp (19*H)) = 32*(exp (6*H)*exp (6*H)) := by
    rw [mul_left_comm, ← exp_add, ← exp_add]
    congr 2
    ring
  unfold CircleCells.width
  rw [← mul_div_assoc, div_le_iff₀ (Nat.cast_pos.mpr (grid_positive H))]
  have bd := mul_le_mul_of_nonneg_left lower (exp_pos (-(7*H))).le
  rw [eqv] at bd
  nlinarith only [bd, sq_nonneg (exp (6*H))]

theorem sample_positive (N : ℕ) (hN : 0 < N) (D : ℝ) (hD : 0 ≤ D) :
    0 < sampleSize N D := Nat.ceil_pos.mpr (by positivity)

theorem rejection_small (N : ℕ) (hN : 0 < N) (D : ℝ) (hD : 0 ≤ D) :
    36*N*(D/(sampleSize N D : ℝ))^(1/4:ℝ) ≤ 1/200 := by
  have u : 0 < 7200*(N:ℝ) := by positivity
  have k : (7200*(N:ℝ))^4*(D+1) ≤ (sampleSize N D : ℝ) := Nat.le_ceil _
  have d : D/(sampleSize N D:ℝ) ≤ (1/(7200*N:ℝ))^4 := by
    rw [div_le_iff₀ (Nat.cast_pos.mpr (sample_positive N hN D hD)), one_div, inv_pow, ← div_eq_inv_mul,
      le_div_iff₀ (pow_pos u 4)]
    nlinarith only [k, (pow_pos u 4).le]
  have z := Real.rpow_le_rpow (div_nonneg hD (Nat.cast_nonneg _)) d (by norm_num : (0:ℝ) ≤ 1/4)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 1/(7200*N:ℝ))] at z
  norm_num at z
  calc
    _ ≤ 36*N*((N:ℝ)⁻¹*(1/7200)) := mul_le_mul_of_nonneg_left z (by positivity)
    _ = 1/200 := by field_simp; norm_num

/-- The small-height endpoint uses this condition directly for its own
atom bound, so it retains the full power saved in the degree estimate. -/
theorem budget_impossible {H D θ : ℝ} (hH : 1000 ≤ H) (hD : 0 ≤ D)
    (hcollision : ((((gridSize H)^4+1)^(sampleSize (gridSize H) D-1) : ℕ) : ℝ)*θ ≤ 1/100) :
    ¬ (1 ≤ ((((gridSize H)^4+1)^(sampleSize (gridSize H) D-1) : ℕ) : ℝ)*θ +
      2/300 + H/(6*H) + (H+3*log 2)/(7*H) +
      36*(gridSize H : ℝ)*(D/(sampleSize (gridSize H) D : ℝ))^(1/4:ℝ)) := by
  have hp : 0 < H := by linarith
  have h₆ : H/(6*H)=1/6 := by field_simp
  have h₇ : (H+3*log 2)/(7*H) ≤ 1/6 := by
    rw [div_le_iff₀ (by positivity)]; linarith [Real.log_two_lt_d9]
  rw [h₆]
  linarith [rejection_small _ (grid_positive H) D hD]


end
end PlanarUnitDistances.BoundedHeight
