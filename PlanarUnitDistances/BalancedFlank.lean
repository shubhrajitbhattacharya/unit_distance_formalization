import PlanarUnitDistances.FlankIntervals
open MeasureTheory Set Finset Filter Real
namespace PlanarUnitDistances.Flanks
noncomputable section
open scoped Classical

/-- The actual tail probability of a real-valued threshold drawn from a finite law. -/
def thresholdTail {X : Type*} [Fintype X] (μ Z : X → ℝ) (s : ℝ) :=
  ∑x,if s<Z x then μ x else 0

def interiorMass {X : Type*} [Fintype X] (μ Z : X → ℝ) (l r : ℝ) :=
  ∑x,if Z x∈Ioo l r then μ x else 0

lemma interiorMass_le {X : Type*} [Fintype X] (μ Z : X → ℝ)
    {l r δ : ℝ} (hδ : 0≤δ) (h : ∀s∈Ioo l r, |thresholdTail μ Z s-1/2|≤δ) :
    interiorMass μ Z l r ≤ 2*δ := by
  classical
  let A := univ.filter (fun x => Z x∈Ioo l r)
  by_cases ha : A.Nonempty
  · obtain ⟨m,hm,hmin⟩ := exists_min_image A Z ha
    obtain ⟨M,hM,hmax⟩ := exists_max_image A Z ha
    have hmi := (mem_filter.mp hm).2
    have hMi := (mem_filter.mp hM).2
    let s := (l+Z m)/2
    have hs₁ : l<s := by dsimp [s]; linarith [hmi.1]
    have hs₂ : s<Z m := by dsimp [s]; linarith [hmi.1]
    have hRange : s∈Ioo l r := ⟨hs₁,hs₂.trans hmi.2⟩
    have hid : interiorMass μ Z l r = thresholdTail μ Z s-thresholdTail μ Z (Z M) := by
      unfold interiorMass thresholdTail
      rw [←sum_sub_distrib]
      apply sum_congr rfl
      intro x _
      by_cases hx : Z x∈Ioo l r
      · have hxA : x∈A := mem_filter.mpr ⟨mem_univ _,hx⟩
        simp only [if_pos hx,if_pos (hs₂.trans_le (hmin x hxA)),if_neg (not_lt.mpr (hmax x hxA)),sub_zero]
      · rw [if_neg hx]
        by_cases hxs : s<Z x
        · have hxM : Z M<Z x := by
            by_contra! hn
            exact hx ⟨hs₁.trans hxs,hn.trans_lt hMi.2⟩
          rw [if_pos hxs,if_pos hxM,sub_self]
        · have hxM : ¬Z M<Z x := by
            intro hxy
            exact hxs (hs₂.trans_le (hmin M hM) |>.trans hxy)
          rw [if_neg hxs,if_neg hxM,sub_zero]
    rw [hid]
    linarith [(abs_le.mp (h s hRange)).2,(abs_le.mp (h (Z M) hMi)).1]
  · have hz : interiorMass μ Z l r=0 := by
      unfold interiorMass
      apply sum_eq_zero
      intro x _
      apply if_neg
      exact fun hx => ha ⟨x,mem_filter.mpr ⟨mem_univ _,hx⟩⟩
    rw [hz]; linarith

/-- On a balanced common window, averaging the indicator that both independent
thresholds lie strictly inside costs at most one fifteenth of the integrated
conditional disagreement. Window length is zero for reversed endpoints. -/
theorem balanced_window_pair_charge {X : Type*} [Fintype X] (μ Z : X → ℝ)
    (hμ : ∀x,0≤μ x) (l r : ℝ)
    (hbal : ∀s∈Ioo l r,|thresholdTail μ Z s-1/2|≤1/sqrt 24) :
    (1/6:ℝ)*max 0 (r-l)* (∑ x,∑ y,if Z x∈Ioo l r ∧ Z y∈Ioo l r then μ x*μ y else 0)
      ≤ (1/15:ℝ)*∫s in Ioo l r,2*thresholdTail μ Z s*(1-thresholdTail μ Z s) := by
  classical
  have hδ : 0≤1/sqrt (24:ℝ) := by positivity
  have hmass := interiorMass_le μ Z hδ hbal
  have hmass0 : 0 ≤ interiorMass μ Z l r := Finset.sum_nonneg (fun x _ => by split_ifs; exact hμ x; exact le_rfl)
  have hsq := (sq_le_sq₀ hmass0 (by positivity)).mpr hmass
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤24)
  have hδsq : (1/Real.sqrt 24)^2=(1/24:ℝ) := by rw [div_pow,hs]; norm_num
  have hsimp : (2*(1/Real.sqrt 24))^2=(1/6:ℝ) := by rw [mul_pow,hδsq]; norm_num
  have hp : (∑ x,∑ y,if Z x∈Ioo l r ∧ Z y∈Ioo l r then μ x*μ y else 0)=
      (interiorMass μ Z l r)^2 := by
    unfold interiorMass
    rw [pow_two,sum_mul]
    apply sum_congr rfl; intro x _
    rw [mul_sum]
    apply sum_congr rfl; intro y _
    by_cases hx : Z x∈Ioo l r <;> by_cases hy : Z y∈Ioo l r <;> simp [hx,hy]
  have hlow (s : ℝ) (hsin : s∈Ioo l r) : (5/12:ℝ) ≤ 2*thresholdTail μ Z s*(1-thresholdTail μ Z s) := by
    have hh := (sq_le_sq₀ (abs_nonneg _) hδ).mpr (hbal s hsin)
    rw [sq_abs,hδsq] at hh
    nlinarith
  have hmeas : Measurable (thresholdTail μ Z) :=
    Finset.measurable_fun_sum _ (fun x _ => Measurable.ite measurableSet_Iio measurable_const measurable_const)
  have hint : IntegrableOn (fun s => 2*thresholdTail μ Z s*(1-thresholdTail μ Z s)) (Ioo l r) := by
    apply IntegrableOn.of_bound measure_Ioo_lt_top
      ((measurable_const.mul hmeas).mul (measurable_const.sub hmeas)).aestronglyMeasurable 1
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hsin
    change ‖2*thresholdTail μ Z s*(1-thresholdTail μ Z s)‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (le_trans (by norm_num) (hlow s hsin))]
    nlinarith [sq_nonneg (thresholdTail μ Z s-1/2)]
  have hInt := setIntegral_mono_on (f:=fun _ : ℝ => (5/12:ℝ))
    (by exact integrableOn_const (measure_Ioo_lt_top.ne)) hint measurableSet_Ioo hlow
  rw [setIntegral_const,Real.volume_real_Ioo,smul_eq_mul,max_comm] at hInt
  rw [hp]
  rw [hsimp] at hsq
  have hmul := mul_le_mul_of_nonneg_left hsq (le_max_left 0 (r-l))
  linarith

end
end PlanarUnitDistances.Flanks
