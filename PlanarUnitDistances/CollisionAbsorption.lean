import PlanarUnitDistances.ComparisonConstants
import PlanarUnitDistances.TemplateDiagonal

namespace PlanarUnitDistances.ComparisonConstants
open Real
noncomputable section

/-- Absorb the global fixed-pair charge and the weighted diagonal charge
into the manuscript's single full-score error. The list-size adjustment
is already included in the collision factor m. -/
theorem collision_absorption {S W X m : ℝ} (large : 2^2100 < S)
    (width : W≤S/dy 1800) (hx : X≤4*S) (mpos : 0≤m) (mass : m≤dy 144000) :
    2*log 2+2*(W+X)*m ≤ dy 144*S := by
  have sp : 0≤S := (pow_pos (by norm_num : (0:ℝ)<2) 2100).le.trans large.le
  have w : W*m≤S*dy 142200 := calc
    _ ≤ (S/dy 1800)*m := mul_le_mul_of_nonneg_right width mpos
    _ ≤ (S/dy 1800)*dy 144000 := mul_le_mul_of_nonneg_left mass (div_nonneg sp (pos _).le)
    _ = _ := by rw [←div 144000 1800 (by decide)]; ring
  have xx : X*m≤4*S*dy 144000 :=
    (mul_le_mul_of_nonneg_right hx mpos).trans (mul_le_mul_of_nonneg_left mass (mul_nonneg (by norm_num) sp))
  have eig (n : ℕ) (le : 148≤n) : S*dy n≤S*dy 148 := mul_le_mul_of_nonneg_left (antitone le) sp
  have dg : dy 144 = 16*dy 148 := by
    have h := mul 144 4
    change dy 144*dy 4=dy 148 at h
    rw [show dy 4=(1/16:ℝ) by norm_num [dy]] at h
    linarith
  have base := mul_le_mul_of_nonneg_right large.le (pos 148).le
  have pow : (2:ℝ)^2100*dy 148=(2:ℝ)^1952 := by
    rw [show (2100:ℕ)=1952+148 by decide,pow_add,dy,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero),mul_one]
  rw [pow] at base
  have two : (2:ℝ)≤2^1952 := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by decide : 1≤1952)
  have logbound := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have cost : 2*log 2 ≤ S*dy 148 := (show 2*log 2≤2 by linarith only [logbound]).trans (two.trans base)
  have w' := w.trans (eig 142200 (by decide))
  have x' : X*m≤4*(S*dy 148) := xx.trans (by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (eig 144000 (by decide)) (by norm_num))
  rw [dg]
  calc
    _ = 2*log 2+2*(W*m+X*m) := by ring
    _ ≤ S*dy 148+2*(S*dy 148+4*(S*dy 148)) :=
      add_le_add cost (mul_le_mul_of_nonneg_left (add_le_add w' x') (by norm_num))
    _ ≤ _ := by nlinarith only [mul_nonneg sp (pos 148).le]

end
end PlanarUnitDistances.ComparisonConstants

namespace OAI.PlanarUnitDistances.FiniteLaw
open Finset
noncomputable section


end
end OAI.PlanarUnitDistances.FiniteLaw
