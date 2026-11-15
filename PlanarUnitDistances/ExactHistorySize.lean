import PlanarUnitDistances.Constants
import PlanarUnitDistances.ComparisonConstants

namespace PlanarUnitDistances.ComparisonConstants
open Real
noncomputable section

def historyDepth (D : ℝ) := ⌈(2:ℝ)^576000*(D+1)⌉₊
theorem historyDepth_pos (D : ℝ) (hd : 0≤D) : 0<historyDepth D :=
  Nat.ceil_pos.mpr (mul_pos (by positivity) (by linarith))
theorem historyDepth_large (D : ℝ) : (2:ℝ)^576000*(D+1)≤(historyDepth D:ℝ) :=
  Nat.le_ceil _

private lemma depth_gap : ((2:ℝ)^576000*exactGap)*(30600*288000) ≤ 1/2 := by
  have hg := exactGap_lt_largeHeightGap.le
  rw [Real.rpow_neg (by norm_num),←Nat.cast_ofNat (R:=ℝ) (n:=594036),Real.rpow_natCast] at hg
  change exactGap≤dy 594036 at hg
  have hd : (2:ℝ)^576000*dy 594036=dy 18036 := by
    rw [←div 594036 576000 (by decide),div_eq_mul_inv,
      show (dy 576000)⁻¹=(2:ℝ)^576000 from inv_inv _,mul_comm]
  have small := (antitone (by decide : 40≤18036))
  calc
    _ ≤ ((2:ℝ)^576000*dy 594036)*(30600*288000) := by gcongr
    _ ≤ dy 40*(30600*288000) := by rw [hd]; gcongr
    _ ≤ _ := by norm_num [dy]

/-- At the exact gap the number of two-coordinate observation histories is
small against the largest point atom. Here the constant k^32 is built into
the chosen depth, with the exact ceiling handled even at an integer. -/
theorem history_atom {t D θ : ℝ} (ht : 1≤t) (hd : 0≤D)
    (hi : D+1≤30600*exactGap*log t) (hθ : θ≤t^(-1:ℝ)) :
    ((2:ℝ)^144000)^(2*(historyDepth D-1))*θ ≤ t^(-(1/2:ℝ)) := by
  let N := historyDepth D
  have ht' : 0<t := zero_lt_one.trans_le ht
  have dep : ((N-1:ℕ):ℝ)≤(2:ℝ)^576000*(D+1) := by
    rw [Nat.cast_sub (historyDepth_pos D hd),Nat.cast_one]
    exact ((sub_lt_iff_lt_add).mpr (Nat.ceil_lt_add_one (show 0≤(2:ℝ)^576000*(D+1) by positivity))).le
  have hl : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have coeff : ((N-1:ℕ):ℝ)*(288000*log 2) ≤ (1/2)*log t := calc
    _ ≤ ((N-1:ℕ):ℝ)*288000 := by gcongr; linarith
    _ ≤ ((2:ℝ)^576000*(30600*exactGap*log t))*288000 := by
      apply mul_le_mul_of_nonneg_right _ (by norm_num)
      exact dep.trans (mul_le_mul_of_nonneg_left hi (by positivity))
    _ = (((2:ℝ)^576000*exactGap)*(30600*288000))*log t := by ac_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right depth_gap (log_nonneg ht)
  have e : ((2:ℝ)^144000)^(2*(N-1))=exp (((N-1:ℕ):ℝ)*(288000*log 2)) := by
    rw [←Real.exp_log (show 0<((2:ℝ)^144000)^(2*(N-1)) by positivity),Real.log_pow,Real.log_pow]
    congr 1
    push_cast; ring
  apply (mul_le_mul_of_nonneg_left hθ (show 0≤((2:ℝ)^144000)^(2*(N-1)) by positivity)).trans
  rw [e,Real.rpow_def_of_pos ht',Real.rpow_def_of_pos ht',←Real.exp_add,exp_le_exp]
  linarith only [coeff]

end
end PlanarUnitDistances.ComparisonConstants
