import PlanarUnitDistances.Rectangle
open Filter
namespace PlanarUnitDistances
noncomputable section

private lemma eventually_const_mul_rpow_le {u v : ℝ} (huv : u<v) (c : ℝ) :
    ∀ᶠ t : ℝ in atTop, c*t^u ≤ t^v := by
  have h := (tendsto_rpow_atTop (sub_pos.mpr huv)).eventually_ge_atTop c
  filter_upwards [h,eventually_gt_atTop (0:ℝ)] with t ht ht0
  calc
    c*t^u ≤ t^(v-u)*t^u := mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg ht0.le _)
    _ = t^v := by rw [← Real.rpow_add ht0]; congr 1; ring

/-- All fixed-g winner fractions and the two singleton deletion tests for the
actual sizes of the trimmed graph. The hypotheses below concern the selected
winner and its ambient vertex counts, so the conclusion applies to that same winner. -/
theorem fixed_winner_scales {g : ℝ} (hg : 0<g) :
    let a := 10000*g
    ∀ᶠ t : ℝ in atTop, ∀ {U V W m n : ℝ},
      t^(-a/8) ≤ U → t^(-a/8) ≤ V → U≤1 → V≤1 →
      (U*V)^(27/50:ℝ) ≤ W →
      W ≤ t^(20*g)*Real.sqrt (U*V)*((U*V)^(1/6:ℝ)+2*t^(-a/2)) →
      t^(1+2*a-13*g) ≤ m → t^(2+a-13*g) ≤ n →
      (2*t^(20*g))^(-(150/19:ℝ)) ≤ U*V ∧ t^(-160*g) ≤ U*V ∧
      t^(-160*g) ≤ U ∧ t^(-160*g) ≤ V ∧ t^(-87*g) ≤ W ∧
      t^(-a/8) ≤ U-1/m ∧ t^(-a/8) ≤ V-1/n := by
  let a := 10000*g
  have eSmall : 20*g-a/2+a/100<0 := by dsimp [a]; linarith
  have hsmall := eventually_const_mul_rpow_le eSmall 4
  have eProd : -(160:ℝ)*g < 20*g*(-(150/19:ℝ)) := by linarith
  have hprod := eventually_const_mul_rpow_le eProd ((2:ℝ)^(150/19:ℝ))
  have edel : -a/8 < -160*g := by dsimp [a]; linarith
  have hdel := eventually_const_mul_rpow_le edel 2
  filter_upwards [hsmall,hprod,hdel,eventually_ge_atTop (1:ℝ)] with t hsmall hprod hdel ht
  have ht0 := zero_lt_one.trans_le ht
  intro U V W m n hu hv hu1 hv1 hW hpre hm hn
  have hτ := Real.rpow_pos_of_pos ht0 (-a/8)
  have hu0 := hτ.trans_le hu
  have hv0 := hτ.trans_le hv
  have hz := mul_pos hu0 hv0
  have hcut := mul_le_mul hu hv hτ.le hu0.le
  have hp := Real.rpow_le_rpow_of_nonpos (mul_pos hτ hτ) hcut (by norm_num : -(1/25:ℝ)≤0)
  have hfpow : (t^(-a/8)*t^(-a/8))^(-(1/25:ℝ)) = t^(a/100) := by
    rw [← Real.rpow_add ht0,← Real.rpow_mul ht0.le]; congr 1; ring
  rw [hfpow] at hp
  have hcalc : 2*t^(20*g)*t^(-a/2)*(U*V)^(-(1/25:ℝ)) ≤ 1/2 := by
    calc
      _ ≤ 2*t^(20*g)*t^(-a/2)*t^(a/100) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = 2*t^(20*g-a/2+a/100) := by rw [show 20*g-a/2+a/100 = (20*g+(-a/2))+a/100 by ring, Real.rpow_add ht0,Real.rpow_add ht0]; ring
      _ ≤ 1/2 := by rw [Real.rpow_zero] at hsmall; linarith
  have hMin := winning_rectangle_product hz (Real.rpow_pos_of_pos ht0 _) (hW.trans hpre) hcalc
  have hscaled : t^(-160*g) ≤ (2*t^(20*g))^(-(150/19:ℝ)) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg ht0.le _),
      ← Real.rpow_mul ht0.le, Real.rpow_neg (by norm_num : (0:ℝ)≤2), inv_mul_eq_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _)).mpr (by linarith)
  have hzMin := hscaled.trans hMin
  have hU := hzMin.trans (mul_le_of_le_one_right hu0.le hv1)
  have hV := hzMin.trans (mul_le_of_le_one_left hv0.le hu1)
  have hWMin : t^(-87*g) ≤ W := by
    have hw := Real.rpow_le_rpow (Real.rpow_nonneg ht0.le _) hzMin (by norm_num : 0≤(27/50:ℝ))
    rw [← Real.rpow_mul ht0.le] at hw
    exact (Real.rpow_le_rpow_of_exponent_le ht (by linarith)).trans (hw.trans hW)
  have hdelany (k z e : ℝ) (hSize : t^e ≤ k) (hexp : -a/8 ≥ -e)
      (hZ : t^(-160*g) ≤ z) : t^(-a/8) ≤ z-1/k := by
    have hk : 0<k := (Real.rpow_pos_of_pos ht0 _).trans_le hSize
    have hr := one_div_le_one_div_of_le (Real.rpow_pos_of_pos ht0 e) hSize
    rw [one_div (t^e),← Real.rpow_neg ht0.le] at hr
    have hpart := hr.trans (Real.rpow_le_rpow_of_exponent_le ht hexp)
    linarith
  exact ⟨hMin,hzMin,hU,hV,hWMin,
    hdelany m U _ hm (by dsimp [a]; linarith) hU,
    hdelany n V _ hn (by dsimp [a]; linarith) hV⟩

end
end PlanarUnitDistances
