import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

namespace PlanarUnitDistances.BinaryDiagonal
open Real Set
noncomputable section

/-- The two equal-label rectangles have counting geometric means z and y.
The lighter rectangle has edge mass at most nine times the mismatch mass. -/
theorem lighter {z y w v s ξ : ℝ} (hz : 0≤z) (hy : 0≤y)
    (hzy : z≤y) (hcs : z+y≤1) (hξ : 0≤ξ) (hsmall : ξ≤1/(2:ℝ)^100)
    (diag : w+v=1-s)
    (rw₁ : w≤z*(z^(2/25:ℝ)+ξ)) (rw₂ : v≤y*(y^(2/25:ℝ)+ξ))
    (low : (54/50:ℝ)*z≤s+2*w) : w≤9*s := by
  let c : ℝ := (1/2:ℝ)^(2/25:ℝ)
  have hc : c ≤ 947/1000 := by
    apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg (by norm_num) _) (by norm_num)
      (by norm_num : (0:ℝ)<25)).mp
    rw [←Real.rpow_mul (by norm_num), show (2/25:ℝ)*25=2 by norm_num]
    norm_num
  have hhalf : z≤1/2 := by linarith
  have hzc := Real.rpow_le_rpow hz hhalf (by norm_num : (0:ℝ)≤2/25)
  change z^(2/25:ℝ)≤c at hzc
  by_cases small : z≤(1/2:ℝ)^(25:ℕ)
  · have pow := Real.rpow_le_rpow hz small (by norm_num : (0:ℝ)≤2/25)
    rw [←Real.rpow_natCast, ←Real.rpow_mul (by norm_num)] at pow
    norm_num at pow
    have bound : z^(2/25:ℝ)+ξ ≤ 27/100 := by norm_num1 at hsmall; linarith
    have ww := rw₁.trans (mul_le_mul_of_nonneg_left bound hz)
    linarith
  · have herror : ξ≤z/10000 := by norm_num1 at small hsmall; linarith
    have secant := (convexOn_rpow (p:=1+(2/25:ℝ)) (by norm_num)).2
      (show (1/2:ℝ) ∈ Ici 0 by norm_num) (show (1:ℝ) ∈ Ici 0 by norm_num)
      (show 0≤2*z by linarith) (show 0≤1-2*z by linarith) (by ring)
    change (2*z*(1/2)+(1-2*z)*1)^(1+(2/25:ℝ)) ≤
      2*z*(1/2:ℝ)^(1+(2/25:ℝ))+(1-2*z)*1^(1+(2/25:ℝ)) at secant
    rw [show 2*z*(1/2)+(1-2*z)*1=1-z by ring, Real.one_rpow,
      Real.rpow_add (by norm_num : (0:ℝ)<1/2), Real.rpow_one] at secant
    have hyp : y*y^(2/25:ℝ) ≤ (1-z)^(1+(2/25:ℝ)) := by
      calc
        _ = y^(1+(2/25:ℝ)) := by rw [Real.rpow_add_of_nonneg hy (by norm_num) (by norm_num),Real.rpow_one]
        _ ≤ _ := Real.rpow_le_rpow hy (by linarith) (by norm_num)
    have hzc' := mul_le_mul_of_nonneg_left hzc hz
    have hzξ := mul_le_mul_of_nonneg_right hcs hξ
    have hzcap := mul_le_mul_of_nonneg_left hc hz
    change (1-z)^(1+(2/25:ℝ))≤2*z*((1/2)*c)+(1-2*z)*1 at secant
    have first : 2*(1-c)*z ≤ s+ξ := by nlinarith only [secant,hyp,rw₁,rw₂,diag,hzc',hzξ]
    have hξ' : ξ≤1/10000 := by norm_num1 at hsmall; linarith
    have hzw := rw₁.trans (mul_le_mul_of_nonneg_left (add_le_add hzc hξ') hz)
    nlinarith only [hzw,first,hzcap,herror,hz]

end
end PlanarUnitDistances.BinaryDiagonal
