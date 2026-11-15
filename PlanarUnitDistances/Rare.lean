import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! # Rare two-edge paths -/
open Finset Real Set MeasureTheory
open scoped BigOperators

namespace PlanarUnitDistances

/-- Tail estimate from the marginal rectangle bound.
The only numbers used for the expansion constants are their common upper bound two. -/
theorem rare_conditional_tail {h s k ξ : ℝ} (hh : 0 ≤ h) (hs : 0 < s) (hk : 0 ≤ k)
    (_hξ : 0 ≤ ξ)
    (hrect : s*k ≤ 2*h^(27/50:ℝ)*k^(27/50:ℝ) + 2*ξ*Real.sqrt (h*k)) :
    k ≤ ((4:ℝ)^(50/23:ℝ)) * h^(27/23:ℝ) / s^(50/23:ℝ) + 16*ξ^2*h/s^2 := by
  by_cases h0 : k = 0
  · subst k
    positivity
  have kp : 0 < k := lt_of_le_of_ne hk (Ne.symm h0)
  by_cases hsmall : s*k ≤ 4*h^(27/50:ℝ)*k^(27/50:ℝ)
  · have scale : k ^ (23/50:ℝ) ≤ 4*h^(27/50:ℝ)/s := by
      apply (le_div_iff₀ hs).2
      apply (le_of_mul_le_mul_right _ (Real.rpow_pos_of_pos kp (27/50:ℝ)))
      calc
        _ = s * (k ^ ((23/50:ℝ)+(27/50:ℝ))) := by rw [Real.rpow_add kp]; ring
        _ = s*k := by norm_num
        _ ≤ _ := hsmall
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg hk _) scale (show (0:ℝ) ≤ 50/23 by norm_num)
    rw [← Real.rpow_mul hk] at hp
    rw [Real.div_rpow (by positivity) hs.le, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hh _),
      ← Real.rpow_mul hh] at hp
    norm_num1 at hp
    rw [Real.rpow_one] at hp
    exact hp.trans (le_add_of_nonneg_right (by positivity : 0 ≤ 16*ξ^2*h/s^2))
  · have hr : s*k ≤ 4*ξ*Real.sqrt (h*k) := by linarith
    have hr2 := mul_self_le_mul_self (mul_nonneg hs.le hk) hr
    have sqroot := Real.sq_sqrt (mul_nonneg hh hk)
    have lhs : k ≤ 16*ξ^2*h/s^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hs)).2
      apply le_of_mul_le_mul_right _ kp
      nlinarith only [hr2, congrArg (fun x : ℝ => 16*ξ^2*x) sqroot]
    exact lhs.trans (le_add_of_nonneg_left (by positivity))

/-- The finite conditional law gives this bound on every positive tail
threshold when the rectangle estimate holds for all subsets of centers. -/
theorem rare_tail_of_rectangles {ι : Type*} [Fintype ι]
    (mass f : ι → ℝ) (h ξ : ℝ) (hm : ∀ i, 0 ≤ mass i) (hh : 0 ≤ h) (hξ : 0 ≤ ξ)
    (hexp : ∀ G : Finset ι, (∑ i ∈ G, mass i * f i) ≤
      2*h^(27/50:ℝ)*(∑ i ∈ G, mass i)^(27/50:ℝ) +
      2*ξ*Real.sqrt (h*(∑ i ∈ G, mass i))) (s : ℝ) (hs : 0 < s) :
    (∑ i, if s ≤ f i then mass i else 0) ≤
      (4:ℝ)^(50/23:ℝ)*h^(27/23:ℝ)/s^(50/23:ℝ) + 16*ξ^2*h/s^2 := by
  classical
  let G := Finset.univ.filter (fun i => s ≤ f i)
  have en : (∑ i, if s ≤ f i then mass i else 0) = ∑ i ∈ G, mass i := by
    simp only [G, Finset.sum_filter]
  rw [en]
  apply rare_conditional_tail hh hs (sum_nonneg (fun i _ => hm i)) hξ
  refine le_trans ?_ (hexp G)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => by
    have hf := (Finset.mem_filter.mp hi).2
    simpa only [mul_comm s] using mul_le_mul_of_nonneg_left hf (hm i)


/-- Squared conditional probability equals the integral of its threshold
events. Include threshold equalities, which has no effect on the integral. -/
theorem rare_second_moment_integral {ι : Type*} [Fintype ι]
    (mass f : ι → ℝ) (hf : ∀ i, f i ∈ Icc (0:ℝ) 1) :
    (∑ i, mass i * (f i)^2) =
      ∫ t in (0:ℝ)..1, ∑ i, if t ≤ f i then 2*t*mass i else 0 := by
  classical
  let F (i : ι) (t : ℝ) := if t ≤ f i then 2*t*mass i else 0
  have intf (i : ι) (a b : ℝ) : IntervalIntegrable (F i) volume a b := by
    rw [intervalIntegrable_iff]
    change IntegrableOn ((Iic (f i)).indicator (fun t => 2*t*mass i)) _ _
    apply (integrableOn_indicator_iff measurableSet_Iic.nullMeasurableSet).2
    have hc : Continuous (fun t : ℝ => 2*t*mass i) := by fun_prop
    exact (intervalIntegrable_iff.mp (hc.intervalIntegrable a b)).mono_set inter_subset_right
  change _ = ∫ t in (0:ℝ)..1, ∑ i, F i t
  rw [intervalIntegral.integral_finsetSum (fun i _ => intf i 0 1)]
  apply Finset.sum_congr rfl
  intro i _
  change _ = ∫ t in (0:ℝ)..1, Set.indicator {t | t ≤ f i} (fun t => 2*t*mass i) t
  rw [intervalIntegral.integral_indicator (hf i), intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const_mul, integral_id]
  ring

/-- The analytic error term in integrating the second tail summand admits
the bound \(r^2\log(1/r)\le3r/8\), uniformly down to zero. -/
theorem rare_log_cutoff {r : ℝ} (hr : 0 < r) : r * Real.log (1/r) ≤ 3/8 := by
  have e8 : (8/3 : ℝ) ≤ Real.exp 1 := by
    have h := Real.sum_le_exp_of_nonneg (x := 1) (by norm_num) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hs := Real.log_le_sub_one_of_pos (div_pos (div_pos zero_lt_one hr) (Real.exp_pos 1))
  rw [Real.log_div (div_ne_zero one_ne_zero hr.ne') (Real.exp_ne_zero _), Real.log_exp] at hs
  have gt := mul_le_mul_of_nonneg_left hs hr.le
  have hc : r * ((1/r)/Real.exp 1) = 1/Real.exp 1 := by field_simp
  have inv : 1/Real.exp 1 ≤ (3/8 : ℝ) := (div_le_iff₀ (Real.exp_pos _)).2 (by linarith)
  linarith


/-- Integrate a Markov bound below a cutoff and a power bound above it.
The two displayed terms in the upper tail are integrated on the same interval. -/
theorem integrate_rare_tails (T : ℝ → ℝ) {r h A C : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hA : 0 ≤ A)
    (hInt : ∀ a b, IntervalIntegrable T volume a b)
    (hlo : ∀ t ∈ Icc 0 r, T t ≤ 2*h)
    (hhi : ∀ t ∈ Icc r 1, T t ≤ 2*A*t ^ (-27/23 : ℝ) + 2*C*t⁻¹) :
    (∫ t in (0:ℝ)..1, T t) ≤
      2*h*r + (23/2:ℝ)*A*r^(-4/23:ℝ) + 2*C*Real.log (1/r) := by
  have low := intervalIntegral.integral_mono_on hr.le (hInt 0 r)
    (intervalIntegrable_const (a := 0) (b := r)) hlo
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at low
  have pi : IntervalIntegrable (fun t : ℝ => t^(-27/23:ℝ)) volume r 1 := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.rpow_const
    intro t ht
    exact Or.inl (ne_of_gt (hr.trans_le ((uIcc_of_le hr1 ▸ ht).1)))
  have ii : IntervalIntegrable (fun t : ℝ => t⁻¹) volume r 1 := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.inv₀
    intro t ht
    exact ne_of_gt (hr.trans_le ((uIcc_of_le hr1 ▸ ht).1))
  have high := intervalIntegral.integral_mono_on hr1 (hInt r 1)
    ((pi.const_mul (2*A)).add (ii.const_mul (2*C))) hhi
  change (∫ t in r..1, T t) ≤ ∫ t in r..1, (2*A*t^(-27/23:ℝ) + 2*C*t⁻¹) at high
  rw [intervalIntegral.integral_add (pi.const_mul _) (ii.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_inv_of_pos hr (by norm_num), integral_rpow (Or.inr ⟨by norm_num,
      notMem_uIcc_of_lt hr (by norm_num)⟩)] at high
  norm_num1 at high
  rw [← intervalIntegral.integral_add_adjacent_intervals (hInt 0 r) (hInt r 1)]
  linarith

/-- Rational-exponent arithmetic at the cutoff. -/
theorem rare_cutoff_arithmetic {h δ r ξ : ℝ} (hh : 0 ≤ h) (hδ : h ≤ δ)
    (hr : 0 < r) (hξ : 0 ≤ ξ) (hξr : ξ ≤ r) (hδr : δ^(4/27:ℝ) ≤ r) :
    2*h*r + (23/2:ℝ)*((4:ℝ)^(50/23:ℝ)*h^(27/23:ℝ))*r^(-4/23:ℝ) +
      2*(16*ξ^2*h)*Real.log (1/r) ≤ 256*h*r := by
  have h4 : (4:ℝ)^(50/23:ℝ) ≤ 21 := by
    apply (Real.rpow_le_rpow_iff (by positivity) (by norm_num) (by norm_num : 0 < (23:ℝ))).mp
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  have hsmall : h ^ (4/27:ℝ) ≤ r :=
    (Real.rpow_le_rpow hh hδ (by norm_num)).trans hδr
  have p := Real.rpow_le_rpow (Real.rpow_nonneg hh _) hsmall (show (0:ℝ) ≤ 27/23 by norm_num)
  rw [← Real.rpow_mul hh] at p
  norm_num1 at p
  have hdecomp : h^(27/23:ℝ) = h*h^(4/23:ℝ) := by
    rw [show (27/23:ℝ) = 1 + 4/23 by norm_num, Real.rpow_add_of_nonneg hh
      (by norm_num) (by norm_num), Real.rpow_one]
  have rdecomp : r^(27/23:ℝ)*r^(-4/23:ℝ) = r := by
    rw [← Real.rpow_add hr]
    norm_num
  have hscale : h^(27/23:ℝ)*r^(-4/23:ℝ) ≤ h*r := by
    rw [hdecomp, mul_assoc]
    have e := mul_le_mul_of_nonneg_right p (Real.rpow_nonneg hr.le (-4/23))
    rw [rdecomp] at e
    exact mul_le_mul_of_nonneg_left e hh
  have a := mul_le_mul_of_nonneg_right h4 (mul_nonneg (Real.rpow_nonneg hh (27/23)) (Real.rpow_nonneg hr.le (-4/23)))
  have b := mul_le_mul_of_nonneg_left hscale (by norm_num : (0:ℝ) ≤ 21)
  by_cases hr1 : r ≤ 1
  · have lg : 0 ≤ Real.log (1/r) := Real.log_nonneg ((le_div_iff₀ hr).2 (by linarith))
    have c := mul_le_mul_of_nonneg_right (mul_self_le_mul_self hξ hξr)
      (mul_nonneg hh lg)
    have d := mul_le_mul_of_nonneg_left (rare_log_cutoff hr) (mul_nonneg hh hr.le)
    nlinarith only [a,b,c,d,mul_nonneg hh hr.le]
  · have lg : Real.log (1/r) ≤ 0 := Real.log_nonpos (by positivity) ((div_le_iff₀ hr).2 (by linarith))
    have c := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2*(16*ξ^2*h)) lg
    nlinarith only [a,b,c,mul_nonneg hh hr.le]


/-- Both neighbors of the same random center land in a small fixed set with
probability at most the manuscript's explicit \`256 h max(δ^(4/27),ξ)\`.
Here \`f i\` is the probability of that set conditional on center \`i\`.
The hypothesis tests the actual weighted center subsets. -/
theorem rare_two_neighbors {ι : Type*} [Fintype ι] (mass f : ι → ℝ)
    (h δ ξ : ℝ) (hm : ∀ i, 0 ≤ mass i) (hf : ∀ i, f i ∈ Icc (0:ℝ) 1)
    (hmean : ∑ i, mass i * f i = h) (hδ : h ≤ δ) (hδ1 : δ ≤ 1)
    (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hexp : ∀ G : Finset ι, (∑ i ∈ G, mass i * f i) ≤
      2*h^(27/50:ℝ)*(∑ i ∈ G, mass i)^(27/50:ℝ) +
      2*ξ*Real.sqrt (h*(∑ i ∈ G, mass i))) :
    (∑ i, mass i * (f i)^2) ≤ 256*h*max (δ^(4/27:ℝ)) ξ := by
  classical
  have hh : 0 ≤ h := hmean ▸ Finset.sum_nonneg (fun i _ => mul_nonneg (hm i) (hf i).1)
  let r := max (δ^(4/27:ℝ)) ξ
  have hd : δ^(4/27:ℝ) ≤ r := le_max_left _ _
  have hx : ξ ≤ r := le_max_right _ _
  have hr1 : r ≤ 1 := max_le (Real.rpow_le_one (hh.trans hδ) hδ1 (by norm_num)) hξ1
  have hhzero (hz : h = 0) : (∑ i, mass i * (f i)^2) ≤ 256*h*r := by
    have g (i : ι) : (f i)^2 ≤ f i := by
      have b := mul_nonneg (hf i).1 (sub_nonneg.mpr (hf i).2)
      nlinarith
    have small := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (g i) (hm i))
    rw [hmean, hz] at small
    simpa [hz] using small
  by_cases hz : h = 0
  · exact hhzero hz
  have hhp := lt_of_le_of_ne hh (Ne.symm hz)
  have hr : 0 < r := (Real.rpow_pos_of_pos (hhp.trans_le hδ) _).trans_le hd
  let T (t : ℝ) := ∑ i, if t ≤ f i then 2*t*mass i else 0
  have intT (a b : ℝ) : IntervalIntegrable T volume a b := by
    let F (i : ι) (t : ℝ) := if t ≤ f i then 2*t*mass i else 0
    have eqT : T = ∑ i, F i := by funext t; simp [T, F, Finset.sum_apply]
    rw [eqT]
    apply IntervalIntegrable.sum
    intro i _
    rw [intervalIntegrable_iff]
    change IntegrableOn ((Iic (f i)).indicator (fun t => 2*t*mass i)) _ _
    apply (integrableOn_indicator_iff measurableSet_Iic.nullMeasurableSet).2
    have hc : Continuous (fun t : ℝ => 2*t*mass i) := by fun_prop
    exact (intervalIntegrable_iff.mp (hc.intervalIntegrable a b)).mono_set inter_subset_right
  have low (t : ℝ) (_ : t ∈ Icc 0 r) : T t ≤ 2*h := by
    dsimp [T]
    rw [← hmean, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hft
    · nlinarith [mul_le_mul_of_nonneg_right hft (hm i)]
    · exact mul_nonneg (by norm_num) (mul_nonneg (hm i) (hf i).1)
  have high (t : ℝ) (ht : t ∈ Icc r 1) : T t ≤
      2*((4:ℝ)^(50/23:ℝ)*h^(27/23:ℝ))*t^(-27/23:ℝ) + 2*(16*ξ^2*h)*t⁻¹ := by
    have tp : 0 < t := hr.trans_le ht.1
    have tail := rare_tail_of_rectangles mass f h ξ hm hh hξ hexp t tp
    have ht' := mul_le_mul_of_nonneg_left tail (by positivity : 0 ≤ 2*t)
    have repr : T t = 2*t*(∑ i, if t ≤ f i then mass i else 0) := by
      dsimp [T]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp)
    rw [repr]
    apply ht'.trans_eq
    have powid : t * (t^(50/23:ℝ))⁻¹ = t^(-27/23:ℝ) := by
      rw [← Real.rpow_neg tp.le]
      calc
        _ = t^(1:ℝ) * t^(-(50/23):ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add tp]; norm_num
    have invid : t * (t^2)⁻¹ = t⁻¹ := by field_simp
    rw [← powid, ← invid]
    ring
  rw [rare_second_moment_integral mass f hf]
  exact (integrate_rare_tails T hr hr1 (by positivity) intT low high).trans
    (rare_cutoff_arithmetic hh hδ hr hξ hx hd)


/-- Convert the marginal rectangle shape in (cb:marginal) into the form
used in the tail argument. Each supplied coefficient may be as large as two. -/
theorem rare_rectangle_power {m h k A B ξ : ℝ} (hh : 0 ≤ h) (hk : 0 ≤ k) (hξ : 0 ≤ ξ)
    (hA : A ≤ 2) (hB : B ≤ 2)
    (hcut : m ≤ Real.sqrt (h*k)*(A*(h*k)^(1/25:ℝ)+B*ξ)) :
    m ≤ 2*h^(27/50:ℝ)*k^(27/50:ℝ) + 2*ξ*Real.sqrt (h*k) := by
  have hhk := mul_nonneg hh hk
  have pw : Real.sqrt (h*k)*(h*k)^(1/25:ℝ) = h^(27/50:ℝ)*k^(27/50:ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add_of_nonneg hhk (by norm_num) (by norm_num)]
    norm_num1
    rw [Real.mul_rpow hh hk]
  refine hcut.trans ?_
  have a := mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hhk (1/25))
  have b := mul_le_mul_of_nonneg_right hB hξ
  have c := mul_le_mul_of_nonneg_left (add_le_add a b) (Real.sqrt_nonneg (h*k))
  nlinarith only [c,pw]


/-- The two numerical multipliers rounding the marginal form of graph
expansion to a coefficient of two. -/
theorem rare_marginal_constants :
    (27/50 : ℝ)^(-(1+2/25):ℝ) ≤ 2 ∧ (27/50:ℝ)⁻¹ ≤ 2 := by
  constructor
  · apply (Real.rpow_le_rpow_iff (by positivity) (by norm_num) (by norm_num : 0 < (25:ℝ))).mp
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  · norm_num

end PlanarUnitDistances

