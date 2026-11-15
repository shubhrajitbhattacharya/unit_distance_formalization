import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace PlanarUnitDistances.Competition.GridRounding
open MeasureTheory Set Real
open scoped Classical
noncomputable section

/-- A single uniform translation parameter may be used on both axes and
for both coordinates. The separation estimate only uses the marginal law. -/
def shift : Measure ℝ := volume.restrict (Ioc 0 1)
instance : IsProbabilityMeasure shift := ⟨by simp [shift,volume_Ioc]⟩

def splitAt (a b u : ℝ) : ℝ := if ⌊a+u⌋=⌊b+u⌋ then 0 else 1

private lemma integrable_split (a b : ℝ) : Integrable (splitAt a b) shift := by
  have hm (x : ℝ) : Measurable (fun u : ℝ => ⌊x+u⌋) := by fun_prop
  have m : Measurable (splitAt a b) :=
    Measurable.ite (measurableSet_eq_fun (hm a) (hm b)) measurable_const measurable_const
  apply Integrable.of_bound m.aestronglyMeasurable 1
  filter_upwards [] with u
  unfold splitAt; split <;> norm_num

private lemma frac_int (a : ℝ) : Integrable (fun u : ℝ => Int.fract (a+u)) shift := by
  have m : Measurable (fun u : ℝ => Int.fract (a+u)) := by fun_prop
  apply Integrable.of_bound m.aestronglyMeasurable 1
  filter_upwards [] with u
  rw [Real.norm_eq_abs,abs_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le

private lemma frac_mean (a : ℝ) : (∫u,Int.fract (a+u) ∂shift)=∫u,Int.fract u ∂shift := by
  have h : Function.Periodic (Int.fract : ℝ → ℝ) 1 := Int.fract_add_one
  change (∫u in Ioc (0:ℝ) 1,Int.fract (a+u))=∫u in Ioc (0:ℝ) 1,Int.fract u
  rw [←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    ←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    intervalIntegral.integral_comp_add_left]
  simpa [add_comm] using h.intervalIntegral_add_eq a 0

private lemma sep_le {a b : ℝ} (h : a≤b) (u : ℝ) :
    splitAt a b u ≤ (b-a)-(Int.fract (b+u)-Int.fract (a+u)) := by
  have hi : ⌊a+u⌋≤⌊b+u⌋ := Int.floor_mono (add_le_add h le_rfl)
  have cancel : (b-a)-(Int.fract (b+u)-Int.fract (a+u))=(⌊b+u⌋:ℝ)-(⌊a+u⌋:ℝ) := by
    simp only [Int.fract]; ring
  rw [cancel]
  unfold splitAt
  split_ifs with eq
  · rw [eq,sub_self]
  · have diff : ⌊a+u⌋+1≤⌊b+u⌋ := by omega
    have cast : (⌊a+u⌋:ℝ)+1≤(⌊b+u⌋:ℝ) := by exact_mod_cast diff
    linarith only [cast]

/-- The probability that two real numbers receive different integer labels
after translating the unit grid is at most their distance. The proof
integrates the difference of floors using periodicity of fractional part. -/
theorem separation (a b : ℝ) : (∫u,splitAt a b u ∂shift) ≤ |a-b| := by
  wlog h : a≤b generalizing a b
  · have eq : splitAt a b=splitAt b a := by funext u; simp only [splitAt,eq_comm]
    rw [eq,abs_sub_comm]
    exact this b a (le_of_not_ge h)
  have mono := integral_mono (integrable_split a b)
    ((integrable_const (b-a)).sub ((frac_int b).sub (frac_int a))) (sep_le h)
  change (∫u,splitAt a b u ∂shift) ≤ ∫u, (b-a)-(Int.fract (b+u)-Int.fract (a+u)) ∂shift at mono
  have isub := integral_sub (integrable_const (μ:=shift) (b-a)) ((frac_int b).sub (frac_int a))
  dsimp only [Pi.sub_apply] at isub
  rw [isub,
    integral_sub (frac_int b) (frac_int a),frac_mean a,frac_mean b,sub_self,sub_zero,integral_const] at mono
  simpa [abs_sub_comm a b,abs_of_nonneg (sub_nonneg.mpr h)] using mono

def square (r : ℝ) (z : ℂ) (u : ℝ) : ℤ×ℤ := (⌊z.re/r+u⌋,⌊z.im/r+u⌋)

def mismatch (r : ℝ) (z w : ℂ) (u : ℝ) : ℝ := if square r z u=square r w u then 0 else 1

lemma measurable_mismatch (r : ℝ) (z w : ℂ) : Measurable (mismatch r z w) := by
  have sm (a : ℂ) : Measurable (square r a) := by unfold square; fun_prop
  exact Measurable.ite (measurableSet_eq_fun (sm z) (sm w)) measurable_const measurable_const

lemma integrable_mismatch (r : ℝ) (z w : ℂ) : Integrable (mismatch r z w) shift := by
  apply Integrable.of_bound (measurable_mismatch ..).aestronglyMeasurable 1
  filter_upwards [] with u
  unfold mismatch; split <;> norm_num

/-- The L1 displacement of the two axes is at most √2 times the complex
distance. Independence between the coordinates of the shift is unnecessary. -/
theorem square_separation {r : ℝ} (hr : 0<r) (z w : ℂ) :
    (∫u,mismatch r z w u ∂shift) ≤ sqrt 2*‖z-w‖/r := by
  have mono := integral_mono (integrable_mismatch r z w)
    ((integrable_split (z.re/r) (w.re/r)).add (integrable_split (z.im/r) (w.im/r))) (by
      intro u
      by_cases h₁ : ⌊z.re/r+u⌋=⌊w.re/r+u⌋ <;> by_cases h₂ : ⌊z.im/r+u⌋=⌊w.im/r+u⌋ <;>
        simp [mismatch,square,splitAt,h₁,h₂])
  change _ ≤ ∫u,splitAt (z.re/r) (w.re/r) u+splitAt (z.im/r) (w.im/r) u ∂shift at mono
  rw [integral_add (integrable_split ..) (integrable_split ..)] at mono
  apply (mono.trans (add_le_add (separation ..) (separation ..))).trans
  rw [←sub_div,←sub_div,abs_div,abs_div,abs_of_pos hr,←add_div]
  apply div_le_div_of_nonneg_right _ hr.le
  have hs := sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hz : ‖z-w‖^2=|z.re-w.re|^2+|z.im-w.im|^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply,sq_abs,sq_abs,Complex.sub_re,Complex.sub_im]; ring
  apply (sq_le_sq₀ (add_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg (sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,hs,hz]
  nlinarith only [sq_nonneg (|z.re-w.re|-|z.im-w.im|)]

end
end PlanarUnitDistances.Competition.GridRounding
