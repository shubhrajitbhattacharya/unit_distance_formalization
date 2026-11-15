import PlanarUnitDistances.WinningScales
open Filter
namespace PlanarUnitDistances
noncomputable section

theorem winning_error_bound {g : ℝ} (hg : 0<g) (ha1 : 10000*g≤1/10) :
    let a := 10000*g
    ∀ᶠ t : ℝ in atTop, ∀ {U V W T : ℝ},
      0≤T → T≤t^(20*g) → t^(-160*g)≤U → t^(-160*g)≤V →
      t^(-160*g)≤U*V → (U*V)^(27/50:ℝ)≤W →
      (T*Real.sqrt (U*V)/W)*((t^(-a/8)/min U V)^(1/6:ℝ)+
        (Real.sqrt (t^(-a))+Real.sqrt (t^(-1:ℝ)))) ≤ t^(-150*g) := by
  let a := 10000*g
  filter_upwards [(tendsto_rpow_atTop (show 0<5*g by linarith)).eventually_ge_atTop (3:ℝ),
    eventually_ge_atTop (1:ℝ)] with t h3 ht
  have ht0 := zero_lt_one.trans_le ht
  intro U V W T hT0 hT hU hV hUV hW
  have hlow := Real.rpow_pos_of_pos ht0 (-160*g)
  have hz := hlow.trans_le hUV
  have hw := (Real.rpow_pos_of_pos hz _).trans_le hW
  have hbase : Real.sqrt (U*V)/W ≤ t^(32*g/5) := by
    calc
      _ ≤ Real.sqrt (U*V)/(U*V)^(27/50:ℝ) :=
        div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos hz _) hW
      _ = (U*V)^(-(1/25:ℝ)) := by rw [Real.sqrt_eq_rpow,← Real.rpow_sub hz]; norm_num
      _ ≤ (t^(-160*g))^(-(1/25:ℝ)) := Real.rpow_le_rpow_of_nonpos hlow hUV (by norm_num)
      _ = t^(32*g/5) := by rw [←Real.rpow_mul ht0.le]; congr 1; ring
  have hcoef : T*Real.sqrt (U*V)/W ≤ t^(20*g+32*g/5) := by
    rw [mul_div_assoc,Real.rpow_add ht0]
    exact mul_le_mul hT hbase (div_nonneg (Real.sqrt_nonneg _) hw.le) (by positivity)
  have hsmall : (t^(-a/8)/min U V)^(1/6:ℝ) ≤ t^((-a/8+160*g)/6) := by
    have hh := div_le_div_of_nonneg_left (Real.rpow_nonneg ht0.le (-a/8)) hlow (le_min hU hV)
    have hh' := Real.rpow_le_rpow (div_nonneg (Real.rpow_nonneg ht0.le _) (hlow.trans_le (le_min hU hV)).le)
      hh (by norm_num : 0≤(1/6:ℝ))
    rw [←Real.rpow_sub ht0,←Real.rpow_mul ht0.le] at hh'
    exact hh'.trans_eq (congrArg (fun x : ℝ => t^x) (by ring))
  have hS (b : ℝ) : Real.sqrt (t^b) = t^(b/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul ht0.le]; congr 1; ring
  have hSa : Real.sqrt (t^(-a)) ≤ t^((-a/8+160*g)/6) := by
    rw [hS]; apply Real.rpow_le_rpow_of_exponent_le ht; dsimp [a]; linarith
  have hS1 : Real.sqrt (t^(-1:ℝ)) ≤ t^((-a/8+160*g)/6) := by
    rw [hS]; apply Real.rpow_le_rpow_of_exponent_le ht; dsimp [a]; linarith
  have hsPos : 0≤(t^(-a/8)/min U V)^(1/6:ℝ) :=
    Real.rpow_nonneg (div_nonneg (Real.rpow_nonneg ht0.le _) (hlow.trans_le (le_min hU hV)).le) _
  have hsum : (t^(-a/8)/min U V)^(1/6:ℝ)+(Real.sqrt (t^(-a))+Real.sqrt (t^(-1:ℝ))) ≤
      3*t^((-a/8+160*g)/6) := by linarith
  have hh := mul_le_mul hcoef hsum (by positivity) (Real.rpow_nonneg ht0.le _)
  apply hh.trans
  calc
    _ = 3*t^(20*g+32*g/5+(-a/8+160*g)/6) := by rw [Real.rpow_add ht0 (20*g+32*g/5) ((-a/8+160*g)/6)]; ring
    _ ≤ 3*t^(-155*g) := by apply mul_le_mul_of_nonneg_left _ (by norm_num); apply Real.rpow_le_rpow_of_exponent_le ht; dsimp [a]; linarith
    _ ≤ t^(5*g)*t^(-155*g) := mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = t^(-150*g) := by rw [←Real.rpow_add ht0]; congr 1; ring

end
end PlanarUnitDistances
