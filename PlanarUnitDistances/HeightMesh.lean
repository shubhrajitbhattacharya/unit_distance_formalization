import Mathlib

/- Adapted from UnitDistances/HeightTransfer.lean, OpenAI math,
commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, Apache-2.0.
The mesh diameter and mismatch bounds here use 3/2, needed for the
manuscript's sharp transfer budget. -/

namespace OAI

namespace PlanarUnitDistances.GridShift
open MeasureTheory Set
open scoped BigOperators
noncomputable section

lemma fract_integrableOn (x a b : ℝ) :
    IntegrableOn (fun u => Int.fract (x+u)) (Icc a b) := by
  apply Integrable.of_bound ((measurable_const.add measurable_id).fract.aestronglyMeasurable) 1
  filter_upwards [] with u
  rw [Real.norm_eq_abs,abs_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le

lemma floor_integrableOn (x a b : ℝ) :
    IntegrableOn (fun u => (⌊x+u⌋ : ℝ)) (Icc a b) := by
  have he : (fun u : ℝ => (⌊x+u⌋ : ℝ)) = fun u => (x+u)-Int.fract (x+u) := by
    funext u
    simp only [Int.fract]
    ring
  rw [he]
  exact (continuous_const.add continuous_id).integrableOn_Icc.sub (fract_integrableOn x a b)

lemma fract_shift_integral (x : ℝ) :
    (∫ u in (0:ℝ)..1, Int.fract (x+u)) = ∫ u in (0:ℝ)..1, Int.fract u := by
  have hp : Function.Periodic (Int.fract : ℝ → ℝ) 1 := Int.fract_add_one
  rw [intervalIntegral.integral_comp_add_left]
  simpa using hp.intervalIntegral_add_eq x 0

lemma floor_difference_integral (x y : ℝ) :
    (∫ u in Icc (0:ℝ) 1, ((⌊y+u⌋:ℝ)-(⌊x+u⌋:ℝ))) = y-x := by
  have he : (fun u : ℝ => ((⌊y+u⌋:ℝ)-(⌊x+u⌋:ℝ))) =
      fun u => (y-x) - (Int.fract (y+u)-Int.fract (x+u)) := by
    funext u
    simp only [Int.fract]
    ring
  have h₁ := integral_sub (μ := volume.restrict (Icc (0:ℝ) 1))
    (show Integrable (fun _ : ℝ => y-x) (volume.restrict (Icc 0 1)) from
      continuous_const.integrableOn_Icc)
    ((fract_integrableOn y 0 1).sub (fract_integrableOn x 0 1))
  have h₂ := integral_sub (fract_integrableOn y 0 1) (fract_integrableOn x 0 1)
  dsimp only [Pi.sub_apply] at h₁ h₂
  rw [he,h₁,h₂]
  have hh (z : ℝ) : (∫ u in Icc (0:ℝ) 1, Int.fract (z+u)) =
      ∫ u in Icc (0:ℝ) 1, Int.fract u := by
    rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
    exact fract_shift_integral z
  rw [hh y,hh x,sub_self,sub_zero]
  simp

def mismatch (x y u : ℝ) : ℝ := if ⌊x+u⌋ = ⌊y+u⌋ then 0 else 1

lemma mismatch_integrableOn (x y a b : ℝ) :
    IntegrableOn (mismatch x y) (Icc a b) := by
  have hm : Measurable (mismatch x y) := Measurable.ite
    (measurableSet_eq_fun (measurable_const.add measurable_id).floor
      (measurable_const.add measurable_id).floor) measurable_const measurable_const
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards [] with u
  unfold mismatch
  split <;> norm_num

lemma mismatch_symm (x y u : ℝ) : mismatch x y u = mismatch y x u := by
  simp only [mismatch,eq_comm]

lemma mismatch_integral_le_abs (x y : ℝ) :
    (∫ u in Icc (0:ℝ) 1, mismatch x y u) ≤ |x-y| := by
  wlog hxy : x ≤ y
  · simpa only [mismatch_symm x y,abs_sub_comm x y] using this y x (le_of_not_ge hxy)
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hxy),← floor_difference_integral x y]
  apply integral_mono (mismatch_integrableOn x y 0 1)
    ((floor_integrableOn y 0 1).sub (floor_integrableOn x 0 1))
  intro u
  have hm := Int.floor_mono (show x+u ≤ y+u by linarith)
  dsimp only [Pi.sub_apply]
  unfold mismatch
  split_ifs with he
  · exact_mod_cast sub_nonneg.mpr hm
  · have hs : ⌊x+u⌋ < ⌊y+u⌋ := lt_of_le_of_ne hm he
    have hz : (1:ℤ) ≤ ⌊y+u⌋-⌊x+u⌋ := by omega
    exact_mod_cast hz


end
end PlanarUnitDistances.GridShift

namespace PlanarUnitDistances.GridShift
open MeasureTheory Set
open scoped BigOperators
noncomputable section

def unitShift : Measure ℝ := volume.restrict (Icc 0 1)
instance : IsProbabilityMeasure unitShift := ⟨by simp [unitShift]⟩
def squareShift : Measure (ℝ × ℝ) := unitShift.prod unitShift
instance : IsProbabilityMeasure squareShift := by unfold squareShift; infer_instance

def gridLabel (r : ℝ) (z : ℂ) (u : ℝ × ℝ) : ℤ × ℤ :=
  (⌊z.re/r+u.1⌋,⌊z.im/r+u.2⌋)

def gridMismatch (r : ℝ) (z w : ℂ) (u : ℝ × ℝ) : ℝ :=
  if gridLabel r z u = gridLabel r w u then 0 else 1

lemma gridLabel_measurable (r : ℝ) (z : ℂ) : Measurable (gridLabel r z) :=
  ((measurable_const.add measurable_fst).floor).prodMk
    ((measurable_const.add measurable_snd).floor)

lemma gridMismatch_measurable (r : ℝ) (z w : ℂ) : Measurable (gridMismatch r z w) :=
  Measurable.ite (measurableSet_eq_fun (gridLabel_measurable r z)
    (gridLabel_measurable r w)) measurable_const measurable_const

lemma gridMismatch_integrable (r : ℝ) (z w : ℂ) :
    Integrable (gridMismatch r z w) squareShift := by
  apply Integrable.of_bound (gridMismatch_measurable r z w).aestronglyMeasurable 1
  filter_upwards [] with u
  unfold gridMismatch
  split <;> norm_num

lemma gridMismatch_le_coordinates (r : ℝ) (z w : ℂ) (u : ℝ × ℝ) :
    gridMismatch r z w u ≤ mismatch (z.re/r) (w.re/r) u.1 +
      mismatch (z.im/r) (w.im/r) u.2 := by
  unfold gridMismatch gridLabel mismatch
  simp only [Prod.mk.injEq]
  split_ifs <;> norm_num at *
  tauto

lemma coordinate_mismatch_measurable (x y : ℝ) : Measurable (mismatch x y) :=
  Measurable.ite (measurableSet_eq_fun (measurable_const.add measurable_id).floor
    (measurable_const.add measurable_id).floor) measurable_const measurable_const

lemma coordinate_mismatch_integrable (x y : ℝ) (i : ℝ × ℝ → ℝ)
    (hi : Measurable i) : Integrable (fun u => mismatch x y (i u)) squareShift := by
  apply Integrable.of_bound ((coordinate_mismatch_measurable x y).comp hi).aestronglyMeasurable 1
  filter_upwards [] with u
  change ‖if ⌊x+i u⌋ = ⌊y+i u⌋ then (0:ℝ) else 1‖ ≤ 1
  split <;> norm_num

lemma integral_mismatch_fst (x y : ℝ) :
    (∫ u, mismatch x y u.1 ∂squareShift) = ∫ u in Icc (0:ℝ) 1, mismatch x y u := by
  rw [squareShift,integral_prod _ (coordinate_mismatch_integrable x y Prod.fst measurable_fst)]
  simp [unitShift]

lemma integral_mismatch_snd (x y : ℝ) :
    (∫ u, mismatch x y u.2 ∂squareShift) = ∫ u in Icc (0:ℝ) 1, mismatch x y u := by
  rw [squareShift,integral_prod _ (coordinate_mismatch_integrable x y Prod.snd measurable_snd)]
  simp [unitShift]

private theorem coordinate_sum (z : ℂ) :
    |z.re| + |z.im| ≤ (3/2:ℝ) * ‖z‖ := by
  have he : ‖z‖^2 = |z.re|^2 + |z.im|^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, sq_abs, sq_abs]; ring
  nlinarith [sq_nonneg (|z.re| - |z.im|), norm_nonneg z, abs_nonneg z.re, abs_nonneg z.im]

lemma gridMismatch_integral_le {r : ℝ} (hr : 0 < r) (z w : ℂ) :
    (∫ u, gridMismatch r z w u ∂squareShift) ≤ min 1 ((3/2:ℝ)*‖z-w‖/r) := by
  apply le_min
  · calc
      _ ≤ ∫ _u, (1:ℝ) ∂squareShift := integral_mono
        (gridMismatch_integrable r z w) (integrable_const _) (by
          intro u; unfold gridMismatch; split <;> norm_num)
      _ = 1 := by simp
  · have h := integral_mono (gridMismatch_integrable r z w)
      ((coordinate_mismatch_integrable (z.re/r) (w.re/r) Prod.fst measurable_fst).add
      (coordinate_mismatch_integrable (z.im/r) (w.im/r) Prod.snd measurable_snd))
      (gridMismatch_le_coordinates r z w)
    have he := integral_add
      (coordinate_mismatch_integrable (z.re/r) (w.re/r) Prod.fst measurable_fst)
      (coordinate_mismatch_integrable (z.im/r) (w.im/r) Prod.snd measurable_snd)
    dsimp only [Pi.add_apply] at h he
    rw [he,integral_mismatch_fst,integral_mismatch_snd] at h
    calc
      _ ≤ |z.re/r-w.re/r| + |z.im/r-w.im/r| := h.trans
        (add_le_add (mismatch_integral_le_abs _ _) (mismatch_integral_le_abs _ _))
      _ = (|(z-w).re|+|(z-w).im|)/r := by
        rw [← sub_div,← sub_div,abs_div,abs_div,abs_of_pos hr,← add_div]
        rfl
      _ ≤ ((3/2:ℝ)*‖z-w‖)/r := div_le_div_of_nonneg_right (coordinate_sum _) hr.le

lemma abs_sub_lt_one_of_floor_eq {x y : ℝ} (h : ⌊x⌋ = ⌊y⌋) : |x-y| < 1 := by
  have hx₁ := Int.floor_le x
  have hx₂ := Int.lt_floor_add_one x
  have hy₁ := Int.floor_le y
  have hy₂ := Int.lt_floor_add_one y
  rw [← h] at hy₁ hy₂
  rw [abs_lt]
  constructor <;> linarith

lemma norm_le_of_same_grid {r : ℝ} (hr : 0 < r) {z w : ℂ} {u : ℝ × ℝ}
    (h : gridLabel r z u = gridLabel r w u) : ‖z-w‖ ≤ (3/2:ℝ)*r := by
  have hx := abs_sub_lt_one_of_floor_eq (congrArg Prod.fst h)
  have hy := abs_sub_lt_one_of_floor_eq (congrArg Prod.snd h)
  rw [add_sub_add_right_eq_sub,← sub_div,abs_div,abs_of_pos hr,div_lt_one hr] at hx hy
  have hsq : ‖z-w‖^2 = |(z-w).re|^2 + |(z-w).im|^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, sq_abs, sq_abs]; ring
  have hu := mul_self_le_mul_self (abs_nonneg _) hx.le
  have hv := mul_self_le_mul_self (abs_nonneg _) hy.le
  simp only [Complex.sub_re, Complex.sub_im] at hsq
  nlinarith [norm_nonneg (z-w)]

lemma tail_le_gridMismatch {r : ℝ} (hr : 0 < r) (z w : ℂ) (u : ℝ × ℝ) :
    (if (3/2:ℝ)*r < ‖z-w‖ then (1:ℝ) else 0) ≤ gridMismatch r z w u := by
  unfold gridMismatch
  split_ifs with hd hg
  · exact (not_le_of_gt hd (norm_le_of_same_grid hr hg)).elim
  all_goals norm_num

end
end PlanarUnitDistances.GridShift

namespace PlanarUnitDistances.GridShift
open MeasureTheory Set Real
noncomputable section

lemma kernel_continuous (a : ℝ) : Continuous (fun s : ℝ => min 1 (a*exp (-s))) :=
  continuous_const.min (continuous_const.mul (Real.continuous_exp.comp continuous_neg))

lemma exp_neg_posLog_control {a : ℝ} (ha : 0 ≤ a) : a*exp (-log⁺ a) ≤ 1 := by
  rw [posLog_eq_log_max_one ha,exp_neg,exp_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
  rw [← div_eq_mul_inv,div_le_one (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
  exact le_max_right _ _

lemma kernel_integral_le {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) :
    (∫ s in (0:ℝ)..T, min 1 (a*exp (-s))) ≤ log⁺ a+1 := by
  have hk (x y : ℝ) : IntervalIntegrable (fun s => min 1 (a*exp (-s))) volume x y :=
    (kernel_continuous a).intervalIntegrable x y
  have he : Continuous (fun s : ℝ => a*exp (-s)) := continuous_const.mul (Real.continuous_exp.comp continuous_neg)
  by_cases h : T ≤ log⁺ a
  · calc
      _ ≤ ∫ _s in (0:ℝ)..T, (1:ℝ) := intervalIntegral.integral_mono_on hT
        (hk _ _) (continuous_const.intervalIntegrable _ _) (fun s _ => min_le_left _ _)
      _ = T := by simp
      _ ≤ log⁺ a+1 := by linarith
  · have hc : log⁺ a ≤ T := (lt_of_not_ge h).le
    rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := log⁺ a) (c := T) (hk _ _) (hk _ _)]
    have h₁ : (∫ s in (0:ℝ)..log⁺ a, min 1 (a*exp (-s))) ≤ log⁺ a := by
      calc
        _ ≤ ∫ _s in (0:ℝ)..log⁺ a, (1:ℝ) := intervalIntegral.integral_mono_on posLog_nonneg
          (hk _ _) (continuous_const.intervalIntegrable _ _) (fun s _ => min_le_left _ _)
        _ = log⁺ a := by simp
    have h₂ : (∫ s in log⁺ a..T, min 1 (a*exp (-s))) ≤ 1 := by
      calc
        _ ≤ ∫ s in log⁺ a..T, a*exp (-s) := intervalIntegral.integral_mono_on hc
          (hk _ _) (he.intervalIntegrable _ _) (fun s _ => min_le_right _ _)
        _ = a*(exp (-log⁺ a)-exp (-T)) := by
          rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_neg,integral_exp]
        _ ≤ a*exp (-log⁺ a) := by nlinarith [exp_pos (-T)]
        _ ≤ 1 := exp_neg_posLog_control ha
    linarith

lemma kernel_setIntegral_le {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) :
    (∫ s in Icc 0 T, min 1 (a*exp (-s))) ≤ log⁺ a+1 := by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hT]
  exact kernel_integral_le ha hT

lemma tail_iff_threshold {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) :
    exp s < a ↔ s < log⁺ a := by
  by_cases h : a ≤ 1
  · have hp : log⁺ a = 0 := (posLog_eq_zero_iff _).mpr (by rwa [abs_of_nonneg ha])
    have he : 1 ≤ exp s := (one_le_exp_iff).mpr hs
    simp only [hp]
    constructor <;> intro hc <;> linarith
  · have hp : log⁺ a = log a := posLog_eq_log (by rw [abs_of_nonneg ha]; linarith)
    rw [hp,lt_log_iff_exp_lt (by linarith)]

lemma tail_integrableOn (a T : ℝ) :
    IntegrableOn (fun s : ℝ => if exp s < a then (1:ℝ) else 0) (Icc 0 T) := by
  apply Integrable.of_bound (Measurable.ite
    (measurableSet_lt measurable_exp measurable_const) measurable_const measurable_const).aestronglyMeasurable 1
  filter_upwards [] with s
  split <;> norm_num

lemma tail_setIntegral {a T : ℝ} (ha : 0 ≤ a) (hT : log⁺ a ≤ T) :
    (∫ s in Icc 0 T, if exp s < a then (1:ℝ) else 0) = log⁺ a := by
  have he : ∀ s ∈ Icc 0 T, (if exp s < a then (1:ℝ) else 0) =
      (Ico (0:ℝ) (log⁺ a)).indicator (fun _ => (1:ℝ)) s := by
    intro s hs
    simp only [tail_iff_threshold ha hs.1]
    simp [Set.indicator,hs.1]
  rw [setIntegral_congr_fun measurableSet_Icc he,integral_indicator_const (1:ℝ) measurableSet_Ico,
    measureReal_restrict_apply measurableSet_Ico]
  have hh : Ico (0:ℝ) (log⁺ a) ⊆ Icc 0 T := fun s hs => ⟨hs.1,hs.2.le.trans hT⟩
  rw [inter_eq_left.mpr hh,Real.volume_real_Ico]
  simp [Real.posLog_nonneg,smul_eq_mul]

end
end PlanarUnitDistances.GridShift

namespace PlanarUnitDistances.LocalHeightTransfer
open MeasureTheory Set Real Finset
open PlanarUnitDistances.GridShift
noncomputable section
variable {P Q : Type} [Fintype P] [Fintype Q]

def left (w : P → Q → ℝ) (p : P) : ℝ := ∑ q, w p q

def dis {A : Type*} [DecidableEq A] (a b : A) : ℝ := if a=b then 0 else 1

def LabelControl (C : ℝ) (w : P → Q → ℝ) : Prop :=
  ∀ L : P ⊕ Q → ℕ,
    (∑ p, ∑ p', left w p * left w p' * dis (L (.inl p)) (L (.inl p'))) ≤
      C * ∑ p, ∑ q, w p q * dis (L (.inl p)) (L (.inr q))

lemma label_control_any {A : Type} [DecidableEq A] {C : ℝ} {w : P → Q → ℝ}
    (hc : LabelControl C w) (L : P ⊕ Q → A) :
    (∑ p, ∑ p', left w p * left w p' * dis (L (.inl p)) (L (.inl p'))) ≤
      C * ∑ p, ∑ q, w p q * dis (L (.inl p)) (L (.inr q)) := by
  classical
  let : Fintype (Set.range L) := Fintype.ofFinite _
  let f : P ⊕ Q → ℕ := fun x => (Fintype.equivFin (Set.range L) ⟨L x,mem_range_self x⟩).val
  have he (x y : P ⊕ Q) : f x = f y ↔ L x = L y := by
    simp only [f,Fin.val_inj,(Fintype.equivFin (Set.range L)).injective.eq_iff,Subtype.mk.injEq]
  simpa only [dis,he] using hc f

omit [Fintype P] in
lemma left_nonneg {w : P → Q → ℝ} (hw : ∀ p q, 0 ≤ w p q) (p : P) :
    0 ≤ left w p := sum_nonneg fun q _ => hw p q

lemma grid_level {C : ℝ} {w : P → Q → ℝ} (hC : 0 ≤ C)
    (hw : ∀ p q, 0 ≤ w p q) (hc : LabelControl C w)
    (z : P ⊕ Q → ℂ) (s : ℝ) :
    (∑ p, ∑ p', left w p * left w p' *
      (if (3/2:ℝ)*exp s < ‖z (.inl p)-z (.inl p')‖ then (1:ℝ) else 0)) ≤
    C * ∑ p, ∑ q, w p q * min 1 ((3/2:ℝ)*‖z (.inl p)-z (.inr q)‖*exp (-s)) := by
  classical
  let f (u : ℝ × ℝ) := ∑ p, ∑ p', left w p * left w p' *
    gridMismatch (exp s) (z (.inl p)) (z (.inl p')) u
  let g (u : ℝ × ℝ) := ∑ p, ∑ q, w p q *
    gridMismatch (exp s) (z (.inl p)) (z (.inr q)) u
  have hf : Integrable f squareShift := integrable_finsetSum _ fun p _ =>
    integrable_finsetSum _ fun p' _ => (gridMismatch_integrable _ _ _).const_mul _
  have hg : Integrable g squareShift := integrable_finsetSum _ fun p _ =>
    integrable_finsetSum _ fun q _ => (gridMismatch_integrable _ _ _).const_mul _
  have hfg (u : ℝ × ℝ) : f u ≤ C*g u := by
    simpa only [f,g,dis,gridMismatch] using
      label_control_any hc (fun x => gridLabel (exp s) (z x) u)
  have hlow (u : ℝ × ℝ) : (∑ p, ∑ p', left w p * left w p' *
      (if (3/2:ℝ)*exp s < ‖z (.inl p)-z (.inl p')‖ then (1:ℝ) else 0)) ≤ f u := by
    apply sum_le_sum; intro p _; apply sum_le_sum; intro p' _
    exact mul_le_mul_of_nonneg_left (tail_le_gridMismatch (exp_pos s) _ _ u)
      (mul_nonneg (left_nonneg hw _) (left_nonneg hw _))
  have hig : (∫ u, g u ∂squareShift) =
      ∑ p, ∑ q, w p q * ∫ u, gridMismatch (exp s) (z (.inl p)) (z (.inr q)) u ∂squareShift := by
    simp only [g,integral_finsetSum _ (fun p _ => integrable_finsetSum _
      (fun q _ => (gridMismatch_integrable _ _ _).const_mul _)),
      integral_finsetSum _ (fun q _ => (gridMismatch_integrable _ _ _).const_mul _),
      integral_const_mul]
  have hupper : (∫ u, g u ∂squareShift) ≤
      ∑ p, ∑ q, w p q * min 1 ((3/2:ℝ)*‖z (.inl p)-z (.inr q)‖*exp (-s)) := by
    rw [hig]
    apply sum_le_sum; intro p _; apply sum_le_sum; intro q _
    apply mul_le_mul_of_nonneg_left _ (hw p q)
    simpa only [exp_neg,div_eq_mul_inv] using gridMismatch_integral_le (exp_pos s)
      (z (.inl p)) (z (.inr q))
  calc
    _ = ∫ _u, (∑ p, ∑ p', left w p * left w p' *
      (if (3/2:ℝ)*exp s < ‖z (.inl p)-z (.inl p')‖ then (1:ℝ) else 0)) ∂squareShift := by simp
    _ ≤ ∫ u, f u ∂squareShift := integral_mono (integrable_const _) hf hlow
    _ ≤ ∫ u, C*g u ∂squareShift := integral_mono hf (hg.const_mul C) hfg
    _ = C * ∫ u, g u ∂squareShift := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hupper hC

lemma weighted_tails_integrable {A : Type*} [Fintype A] (w x : A → ℝ) (T : ℝ) :
    IntegrableOn (fun s => ∑ a, w a * if exp s < x a then (1:ℝ) else 0) (Icc 0 T) :=
  integrable_finsetSum _ fun a _ => (tail_integrableOn (x a) T).const_mul (w a)

lemma weighted_tails_integral {A : Type*} [Fintype A] (w x : A → ℝ)
    (hx : ∀ a, 0 ≤ x a) {T : ℝ} (hT : ∀ a, log⁺ (x a) ≤ T) :
    (∫ s in Icc 0 T, ∑ a, w a * if exp s < x a then (1:ℝ) else 0) =
      ∑ a, w a * log⁺ (x a) := by
  rw [integral_finsetSum _ (fun a _ => (tail_integrableOn (x a) T).const_mul (w a))]
  apply sum_congr rfl; intro a _
  rw [integral_const_mul,tail_setIntegral (hx a) (hT a)]

lemma weighted_kernel_integrable {A : Type*} [Fintype A] (w x : A → ℝ) (T : ℝ) :
    IntegrableOn (fun s => ∑ a, w a * min 1 (x a*exp (-s))) (Icc 0 T) :=
  integrable_finsetSum _ fun a _ => ((kernel_continuous (x a)).integrableOn_Icc).const_mul (w a)

lemma weighted_kernel_integral_le {A : Type*} [Fintype A] (w x : A → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hx : ∀ a, 0 ≤ x a) {T : ℝ} (hT : 0 ≤ T) :
    (∫ s in Icc 0 T, ∑ a, w a * min 1 (x a*exp (-s))) ≤
      ∑ a, w a * (log⁺ (x a)+1) := by
  rw [integral_finsetSum _ (fun a _ => ((kernel_continuous (x a)).integrableOn_Icc).const_mul (w a))]
  apply sum_le_sum; intro a _
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (kernel_setIntegral_le (hx a) hT) (hw a)

lemma log_mesh_control (a : ℝ) : log⁺ a ≤ log⁺ (a/(3/2))+log (3/2) := by
  have h : a = a/(3/2)*(3/2) := by ring
  calc
    _ = log⁺ (a/(3/2)*(3/2)) := congrArg (fun x => log⁺ x) h
    _ ≤ log⁺ (a/(3/2))+log⁺ (3/2:ℝ) := posLog_mul
    _ = _ := by rw [posLog_eq_log (by norm_num : (1:ℝ) ≤ |3/2|)]

lemma archimedean_transfer {C : ℝ} {w : P → Q → ℝ} (hC : 0 ≤ C)
    (hw : ∀ p q, 0 ≤ w p q) (hs : ∑ p, ∑ q, w p q = 1)
    (hc : LabelControl C w) (z : P ⊕ Q → ℂ) :
    (∑ p, ∑ p', left w p * left w p' * log⁺ ‖z (.inl p)-z (.inl p')‖) ≤
    C * ((∑ p, ∑ q, w p q * log⁺ ‖z (.inl p)-z (.inr q)‖)+log (3/2)+1)+log (3/2) := by
  classical
  let a : P × P → ℝ := fun x => ‖z (.inl x.1)-z (.inl x.2)‖/(3/2)
  let b : P × Q → ℝ := fun x => (3/2:ℝ)*‖z (.inl x.1)-z (.inr x.2)‖
  let v : P × P → ℝ := fun x => left w x.1 * left w x.2
  let e : P × Q → ℝ := fun x => w x.1 x.2
  obtain ⟨T,hT⟩ := Finite.exists_le (fun x : P × P => log⁺ (a x))
  let D := max 0 T
  have hD : 0 ≤ D := le_max_left _ _
  have ha (x) : 0 ≤ a x := div_nonneg (norm_nonneg _) (by norm_num)
  have hb (x) : 0 ≤ b x := mul_nonneg (by norm_num) (norm_nonneg _)
  have he (x) : 0 ≤ e x := hw _ _
  have hv (x) : 0 ≤ v x := mul_nonneg (left_nonneg hw _) (left_nonneg hw _)
  have hl (s : ℝ) : (∑ x, v x * if exp s < a x then (1:ℝ) else 0) ≤
      C * ∑ x, e x * min 1 (b x*exp (-s)) := by
    simpa only [Fintype.sum_prod_type,a,b,v,e,lt_div_iff₀ (by norm_num : (0:ℝ)<3/2),
      mul_comm (exp s) (3/2)] using grid_level hC hw hc z s
  have hi := setIntegral_mono_on (weighted_tails_integrable v a D)
    ((weighted_kernel_integrable e b D).const_mul C) measurableSet_Icc (fun s _ => hl s)
  rw [weighted_tails_integral v a ha (fun x => (hT x).trans (le_max_right _ _)),
    integral_const_mul] at hi
  have hib := hi.trans (mul_le_mul_of_nonneg_left
    (weighted_kernel_integral_le e b he hb hD) hC)
  have hsum : ∑ p, left w p = 1 := hs
  have hvsum : ∑ x, v x = 1 := by
    simp only [v,Fintype.sum_prod_type,← mul_sum,hsum,mul_one]
  have hesum : ∑ x, e x = 1 := by
    change (∑ x : P × Q, w x.1 x.2) = 1
    rw [Fintype.sum_prod_type]; exact hs
  have haBound : (∑ p, ∑ p', left w p * left w p' * log⁺ ‖z (.inl p)-z (.inl p')‖) ≤
      (∑ x, v x * log⁺ (a x))+log (3/2) := by
    calc
      _ ≤ ∑ p, ∑ p', left w p * left w p' * (log⁺ (a (p,p'))+log (3/2)) := by
        apply sum_le_sum; intro p _; apply sum_le_sum; intro p' _
        exact mul_le_mul_of_nonneg_left (log_mesh_control _) (hv (p,p'))
      _ = _ := by
        rw [← Fintype.sum_prod_type (fun x : P × P => v x*(log⁺ (a x)+log (3/2)))]
        simp only [mul_add,sum_add_distrib,← sum_mul,hvsum,one_mul]
  have hbBound : (∑ x, e x*(log⁺ (b x)+1)) ≤
      (∑ p, ∑ q, w p q*log⁺ ‖z (.inl p)-z (.inr q)‖)+log (3/2)+1 := by
    calc
      _ ≤ ∑ x, e x * (log⁺ ‖z (.inl x.1)-z (.inr x.2)‖+log (3/2)+1) := by
        apply sum_le_sum; intro x _; apply mul_le_mul_of_nonneg_left _ (he x)
        have hp : log⁺ (b x) ≤ log⁺ ‖z (.inl x.1)-z (.inr x.2)‖+log (3/2) := by
          have h := posLog_mul (x := 3/2) (y := ‖z (.inl x.1)-z (.inr x.2)‖)
          rw [posLog_eq_log (by norm_num : (1:ℝ) ≤ |3/2|)] at h
          simpa only [b,add_comm] using h
        linarith
      _ = _ := by
        simp only [mul_add,sum_add_distrib,← sum_mul,mul_one,hesum,one_mul]
        rw [Fintype.sum_prod_type]
  linarith [mul_le_mul_of_nonneg_left hbBound hC]

lemma nonarchimedean_level {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) {C : ℝ} {w : P → Q → ℝ}
    (hc : LabelControl C w) (z : P ⊕ Q → K) (s : ℝ) :
    (∑ p, ∑ p', left w p * left w p' *
      (if exp s < v (z (.inl p)-z (.inl p')) then (1:ℝ) else 0)) ≤
    C * ∑ p, ∑ q, w p q *
      (if exp s < v (z (.inl p)-z (.inr q)) then (1:ℝ) else 0) := by
  classical
  let R : Setoid (P ⊕ Q) :=
    { r := fun x y => v (z x-z y) ≤ exp s
      iseqv := ⟨by intro x; simpa using (exp_pos s).le,
        by intro x y h; rwa [v.map_sub],
        by
          intro x y z' h₁ h₂
          have he : z x-z z' = (z x-z y)+(z y-z z') := by ring
          rw [he]
          exact (hv _ _).trans (max_le h₁ h₂)⟩ }
  have he (x y : P ⊕ Q) : dis (Quotient.mk R x) (Quotient.mk R y) =
      (if exp s < v (z x-z y) then (1:ℝ) else 0) := by
    simp only [dis,Quotient.eq]
    change (if v (z x-z y) ≤ exp s then (0:ℝ) else 1) = _
    split_ifs <;> norm_num at * <;> linarith
  simpa only [he] using label_control_any hc (Quotient.mk R)

lemma nonarchimedean_transfer {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) {C : ℝ} {w : P → Q → ℝ}
    (hc : LabelControl C w) (z : P ⊕ Q → K) :
    (∑ p, ∑ p', left w p * left w p' * log⁺ (v (z (.inl p)-z (.inl p')))) ≤
    C * ∑ p, ∑ q, w p q * log⁺ (v (z (.inl p)-z (.inr q))) := by
  classical
  let a : P × P → ℝ := fun x => v (z (.inl x.1)-z (.inl x.2))
  let b : P × Q → ℝ := fun x => v (z (.inl x.1)-z (.inr x.2))
  let μ : P × P → ℝ := fun x => left w x.1 * left w x.2
  let e : P × Q → ℝ := fun x => w x.1 x.2
  obtain ⟨T,hT⟩ := Finite.exists_le (fun x : P × P => log⁺ (a x))
  obtain ⟨S,hS⟩ := Finite.exists_le (fun x : P × Q => log⁺ (b x))
  let D := max T S
  have hl (s : ℝ) : (∑ x, μ x * if exp s < a x then (1:ℝ) else 0) ≤
      C * ∑ x, e x * if exp s < b x then (1:ℝ) else 0 := by
    simpa only [Fintype.sum_prod_type,a,b,μ,e] using nonarchimedean_level v hv hc z s
  have hi := setIntegral_mono_on (weighted_tails_integrable μ a D)
    ((weighted_tails_integrable e b D).const_mul C) measurableSet_Icc (fun s _ => hl s)
  rw [weighted_tails_integral μ a (fun x => v.nonneg _) (fun x => (hT x).trans (le_max_left _ _)),
    integral_const_mul,weighted_tails_integral e b (fun x => v.nonneg _)
      (fun x => (hS x).trans (le_max_right _ _))] at hi
  simpa only [Fintype.sum_prod_type,a,b,μ,e] using hi


end
end PlanarUnitDistances.LocalHeightTransfer

end OAI
