import PlanarUnitDistances.GridRounding
import Mathlib.MeasureTheory.Integral.Average

namespace PlanarUnitDistances.Competition.GridRounding
open MeasureTheory Real Set
open scoped Classical
noncomputable section

private lemma axis_diameter {a b r u : ℝ} (hr : 0<r) (h : ⌊a/r+u⌋=⌊b/r+u⌋) : |a-b|≤r := by
  have la := Int.floor_le (a/r+u)
  have lb := Int.floor_le (b/r+u)
  have ua := Int.lt_floor_add_one (a/r+u)
  have ub := Int.lt_floor_add_one (b/r+u)
  rw [h] at la ua
  have ab : |a/r-b/r|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
  rwa [←sub_div,abs_div,abs_of_pos hr,div_le_one hr] at ab

theorem square_diameter {r : ℝ} (hr : 0<r) {z w : ℂ} {u : ℝ}
    (h : square r z u=square r w u) : ‖z-w‖≤sqrt 2*r := by
  have hx : |z.re-w.re|≤r := axis_diameter (u:=u) hr (congrArg Prod.fst h)
  have hy : |z.im-w.im|≤r := axis_diameter (u:=u) hr (congrArg Prod.snd h)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) hr.le)).mp
  rw [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,mul_pow,sq_sqrt (by norm_num : (0:ℝ)≤2)]
  have x := pow_le_pow_left₀ (abs_nonneg _) hx 2
  have y := pow_le_pow_left₀ (abs_nonneg _) hy 2
  rw [sq_abs] at x y
  nlinarith only [x,y]

def failure (n : ℝ) (z z' w w' : ℂ) (s u : ℝ) : ℝ :=
  if (if s<n then square (exp (-s)) z u=square (exp (-s)) z' u ∧ square (exp s) w u≠square (exp s) w' u
      else square (exp s) w u=square (exp s) w' u ∧ square (exp (-s)) z u≠square (exp (-s)) z' u)
    then 0 else 1

lemma failure_bounds (n : ℝ) (z z' w w' : ℂ) (s u : ℝ) : 0≤failure n z z' w w' s u ∧ failure n z z' w w' s u≤1 := by
  unfold failure; split_ifs <;> norm_num

lemma failure_measurable (n : ℝ) (z z' w w' : ℂ) : Measurable (fun x : ℝ×ℝ => failure n z z' w w' x.1 x.2) := by
  have sm (p : ℂ) : Measurable (fun x : ℝ×ℝ => square (exp x.1) p x.2) := by unfold square; fun_prop
  have rev (p : ℂ) : Measurable (fun x : ℝ×ℝ => square (exp (-x.1)) p x.2) :=
    (sm p).comp (measurable_fst.neg.prodMk measurable_snd)
  let A := {x : ℝ×ℝ | square (exp (-x.1)) z x.2=square (exp (-x.1)) z' x.2}
  let B := {x : ℝ×ℝ | square (exp x.1) w x.2=square (exp x.1) w' x.2}
  have hA : MeasurableSet A := measurableSet_eq_fun (rev z) (rev z')
  have hB : MeasurableSet B := measurableSet_eq_fun (sm w) (sm w')
  have eq : {x : ℝ×ℝ | if x.1<n then x∈A ∧ x∉B else x∈B ∧ x∉A} =
      {x : ℝ×ℝ | x.1<n}.ite (A∩Bᶜ) (B∩Aᶜ) := by
    ext x; by_cases hx : x.1<n <;> simp [Set.ite,hx]
  apply Measurable.ite _ measurable_const measurable_const
  change MeasurableSet {x : ℝ×ℝ | if x.1<n then x∈A ∧ x∉B else x∈B ∧ x∉A}
  rw [eq]
  exact MeasurableSet.ite (measurableSet_lt measurable_fst measurable_const) (hA.inter hB.compl) (hB.inter hA.compl)

/-- For small |s−n| the exponential majorant alone dominates one. Outside
that interval the long jump cannot fit in any cell, and the event of an
inconsistent edge is just the separation of the short jump. -/
theorem expected_failure {n : ℝ} {z z' w w' : ℂ} (hz : ‖z-z'‖=exp (-n)) (hw : ‖w-w'‖=exp n) (s : ℝ) :
    (∫u,failure n z z' w w' s u ∂shift) ≤ sqrt 2*exp (-|s-n|) := by
  by_cases near : 1≤sqrt 2*exp (-|s-n|)
  · apply le_trans _ near
    have i : Integrable (failure n z z' w w' s) shift := by
      apply Integrable.of_bound (((failure_measurable ..).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) 1
      filter_upwards [] with u
      change ‖failure n z z' w w' s u‖≤1
      rw [Real.norm_eq_abs,abs_of_nonneg (failure_bounds ..).1]
      exact (failure_bounds ..).2
    simpa using integral_mono i (integrable_const (μ:=shift) (1:ℝ)) (fun u => (failure_bounds n z z' w w' s u).2)
  have far := lt_of_not_ge near
  by_cases h : s<n
  · rw [abs_of_neg (sub_neg.mpr h),neg_neg,exp_sub] at far ⊢
    have long : sqrt 2*exp s<‖w-w'‖ := by
      rw [hw]; rw [←mul_div_assoc,div_lt_one (exp_pos n)] at far; exact far
    have eq : failure n z z' w w' s=mismatch (exp (-s)) z z' := by
      funext u
      have sep : square (exp s) w u≠square (exp s) w' u := fun eq => (not_le_of_gt long) (square_diameter (exp_pos _) eq)
      simp [failure,mismatch,h,sep]
    rw [eq]
    apply (square_separation (exp_pos _) z z').trans_eq
    rw [hz,exp_neg,exp_neg,div_eq_mul_inv,inv_inv]; ring
  · have hle : n≤s := le_of_not_gt h
    rw [abs_of_nonneg (sub_nonneg.mpr hle),neg_sub,exp_sub] at far ⊢
    have long : sqrt 2*exp (-s)<‖z-z'‖ := by
      rw [hz,exp_neg,exp_neg]
      rw [←mul_div_assoc,div_lt_one (exp_pos s)] at far
      rw [←div_eq_mul_inv,←one_div,div_lt_div_iff₀ (exp_pos s) (exp_pos n)]
      simpa using far
    have eq : failure n z z' w w' s=mismatch (exp s) w w' := by
      funext u
      have sep : square (exp (-s)) z u≠square (exp (-s)) z' u := fun eq => (not_le_of_gt long) (square_diameter (exp_pos _) eq)
      simp [failure,mismatch,h,sep]
    rw [eq]
    apply (square_separation (exp_pos _) w w').trans_eq
    rw [hw]; ring

end
end PlanarUnitDistances.Competition.GridRounding
