import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Quantitative rectangle restriction in Proposition `cb:finite-piece`.
All masses and vertex fractions in this module are real; the hypotheses
identify which estimates belong to the ambient rectangle and which to the
selected rectangle. -/

noncomputable section

namespace PlanarUnitDistances

private theorem min_le_geometric (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min a b ≤ Real.sqrt (a * b) := by
  apply Real.le_sqrt_of_sq_le
  rcases le_total a b with h | h
  · rw [min_eq_left h, sq]
    gcongr
  · rw [min_eq_right h, sq]
    gcongr

/-- Convert the two linear terms of the incidence estimate into the
square-root remainder. In the application x=t^(-a) and y=t^(-1). -/
theorem trim_linear_terms {u v w T x y : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hT : 0 < T) (hy : 0 ≤ y) (hyx : y ≤ x)
    (hinc : w ≤ T * ((u * v) ^ (2 / 3 : ℝ) + x * v + y * u))
    (hdegree : w ≤ T * min u v) :
    w ≤ T * Real.sqrt (u * v) * ((u * v) ^ (1 / 6 : ℝ) + 2 * Real.sqrt x) := by
  have huv : 0 ≤ u * v := mul_nonneg hu hv
  have hx := hy.trans hyx
  have hinc' := (div_le_iff₀ hT).mpr (hinc.trans_eq (mul_comm T _))
  have hdegree' := (div_le_iff₀ hT).mpr (hdegree.trans_eq (mul_comm T _))
  have hlinear : w / T ≤ (u * v) ^ (2 / 3 : ℝ) + min u (x * v) + min v (y * u) := by
    have hmain := Real.rpow_nonneg huv (2 / 3 : ℝ)
    have h₁ := hdegree'.trans (min_le_left _ _)
    have h₂ := hdegree'.trans (min_le_right _ _)
    have hxv := mul_nonneg hx hv
    have hyu := mul_nonneg hy hu
    rcases le_total u (x * v) with h | h
    · rw [min_eq_left h]
      have hmin : 0 ≤ min v (y*u) := le_min hv hyu
      linarith
    · rw [min_eq_right h]
      rcases le_total v (y*u) with k | k
      · rw [min_eq_left k]; linarith
      · rw [min_eq_right k]; exact hinc'
  have hm₁ : min u (x * v) ≤ Real.sqrt x * Real.sqrt (u * v) := by
    rw [← Real.sqrt_mul hx, show x * (u * v) = u * (x * v) by ring]
    exact min_le_geometric _ _ hu (mul_nonneg hx hv)
  have hm₂ : min v (y * u) ≤ Real.sqrt x * Real.sqrt (u * v) := by
    calc
      _ ≤ Real.sqrt (v * (y * u)) := min_le_geometric _ _ hv (mul_nonneg hy hu)
      _ = Real.sqrt y * Real.sqrt (u * v) := by
        rw [← Real.sqrt_mul hy, show v * (y * u) = y * (u * v) by ring]
      _ ≤ _ := by gcongr
  have hpow : (u * v) ^ (2 / 3 : ℝ) = Real.sqrt (u * v) * (u * v) ^ (1 / 6 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add' huv (by norm_num : (1 / 2 : ℝ) + 1 / 6 ≠ 0)]
    norm_num
  rw [hpow] at hlinear
  have h := (div_le_iff₀ hT).mp (show w / T ≤ Real.sqrt (u*v) *
    ((u*v) ^ (1/6 : ℝ) + 2 * Real.sqrt x) by linarith)
  linarith

/-- Positivity of the winner and a small second term force a lower bound on
its product UV. This is the inversion producing the factor 150/19. -/
theorem winning_rectangle_product {z T b : ℝ} (hz : 0 < z) (hT : 0 < T)
    (hwin : z ^ (27 / 50 : ℝ) ≤ T * Real.sqrt z * (z ^ (1/6 : ℝ) + 2*b))
    (hsmall : 2*T*b*z^(-(1/25 : ℝ)) ≤ 1/2) :
    (2*T)^(-(150/19 : ℝ)) ≤ z := by
  have hp := Real.rpow_pos_of_pos hz (27/50 : ℝ)
  have heq₁ : z^(27/50 : ℝ) * z^(19/150 : ℝ) = Real.sqrt z * z^(1/6 : ℝ) := by
    rw [← Real.rpow_add hz, Real.sqrt_eq_rpow, ← Real.rpow_add hz]
    norm_num
  have heq₂ : z^(27/50 : ℝ) * z^(-(1/25 : ℝ)) = Real.sqrt z := by
    rw [← Real.rpow_add hz, Real.sqrt_eq_rpow]; norm_num
  have hdivide : 1 ≤ T*z^(19/150 : ℝ) + 2*T*b*z^(-(1/25 : ℝ)) := by
    apply (mul_le_mul_iff_right₀ hp).mp
    rw [mul_one]
    calc
      _ ≤ _ := hwin
      _ = T * (Real.sqrt z * z^(1/6 : ℝ)) + 2*T*b*Real.sqrt z := by ring
      _ = _ := by rw [← heq₁, ← heq₂]; ring
  have hsmall' : (2*T)⁻¹ ≤ z^(19/150 : ℝ) := by
    rw [← one_div, div_le_iff₀ (by positivity : 0 < 2*T)]; linarith
  have h := Real.rpow_le_rpow (by positivity) hsmall' (by norm_num : (0:ℝ) ≤ 150/19)
  rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
    ← Real.rpow_mul hz.le, show (19/150 : ℝ)*(150/19) = 1 by norm_num, Real.rpow_one] at h
  exact h


end PlanarUnitDistances
