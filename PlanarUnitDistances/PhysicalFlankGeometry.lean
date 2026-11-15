import PlanarUnitDistances.GlobalConditionalFlanks
import PlanarUnitDistances.MeasurableFlank

namespace PlanarUnitDistances.Flanks
open Set Real Finset MeasureTheory NumberField OAI.PlanarUnitDistances PosteriorPlaces
open scoped Classical
noncomputable section
variable {K I : Type*} [Field K] [NumberField K] [Fintype I]

private theorem arch_match_bound (v : InfinitePlace K) (u : ℝ×ℝ) (x y : K) {s : ℝ}
    (h : archMatch v u x y s) : v.1 (x-y)≤exp (s+log 2) := by
  by_cases e : x=y
  · simpa [e] using (Real.exp_pos (s+log 2)).le
  have hb := arch_log_bound v u e h
  have sq : sqrt 2≤2 := by nlinarith [sq_sqrt (by norm_num : (0:ℝ)≤2)]
  have ls : log (sqrt 2)≤log 2 := log_le_log (by positivity) sq
  have le : log (v.1 (x-y)) ≤ s+log 2 := hb.trans (add_le_add (le_refl s) ls)
  exact (log_le_iff_le_exp (v.1.pos (sub_ne_zero.mpr e))).mp le

/-- Direction of a neighbor measured from the base of the experiment. -/
def neighborDirection (b : K) (z : I → K) (i : I) := z i-b

private theorem reciprocal_value {b u : K} {z w : I → K}
    (circle : ∀i,(z i-b)*(w i-u)=1) (i : I) : (neighborDirection b z i)⁻¹=w i-u :=
  inv_eq_of_mul_eq_one_right (circle i)

private theorem direction_inj {b : K} {z : I → K} (inj : Function.Injective z) :
    Function.Injective (neighborDirection b z) := fun _ _ e => inj (sub_left_inj.mp e)

/-- At an infinite place the event of an equal shifted-grid label on the
two neighbors is evaluated at their original absolute positions. The base
translation is used only for their field differences and edge thresholds. -/
def archGeometry (μ : I → ℝ) {b u : K} (z w : I → K) (inj : Function.Injective z)
    (circle : ∀i,(z i-b)*(w i-u)=1) (v : InfinitePlace K) (az aw : ℝ×ℝ) (lo hi ε : ℝ)
    (f : ℝ → ℝ) (hf : Antitone f) (keep : I → I → ℝ → Prop)
    (meas : ∀i j,MeasurableSet {s | keep i j s}) :
    LocalComparison μ (neighborDirection b z) v.1 ε (log 2) where
  lo := lo
  hi := hi
  globalTail := f
  antitone := hf
  direct := fun i j s => archMatch v az (z i) (z j) (-s)
  reciprocal := fun i j s => archMatch v aw (w i) (w j) s
  keep := keep
  flank_nonnegative := fun i j ne => BudgetPlaces.alpha_add_log_two_nonneg v.1
    (left_ne_zero_of_mul_eq_one (circle i)) (left_ne_zero_of_mul_eq_one (circle j))
    ((direction_inj inj).ne ne)
  direct_bound := by
    intro i j s h
    have e : neighborDirection b z i-neighborDirection b z j=z i-z j := by unfold neighborDirection; ring
    rw [e]; exact arch_match_bound v az _ _ h
  reciprocal_bound := by
    intro i j s h
    rw [reciprocal_value circle,reciprocal_value circle,sub_sub_sub_cancel_right]
    exact arch_match_bound v aw _ _ h
  integrable := fun i j _ => positive_integrable hf.measurable (measurable_thresholdTail ..)
    (arch_meas v az _ _ (fun s => -s) measurable_neg) (arch_meas v aw _ _ id measurable_id) (meas i j)

/-- At a finite place the same construction uses the exact closed
nonarchimedean balls, with geometric constant zero. -/
def finiteGeometry (μ : I → ℝ) {b u : K} (z w : I → K) (inj : Function.Injective z)
    (circle : ∀i,(z i-b)*(w i-u)=1) (v : FinitePlace K) (lo hi ε : ℝ)
    (f : ℝ → ℝ) (hf : Antitone f) (keep : I → I → ℝ → Prop)
    (meas : ∀i j,MeasurableSet {s | keep i j s}) :
    LocalComparison μ (neighborDirection b z) v.1 ε 0 where
  lo := lo
  hi := hi
  globalTail := f
  antitone := hf
  direct := fun i j s => finiteMatch v (z i) (z j) (-s)
  reciprocal := fun i j s => finiteMatch v (w i) (w j) s
  keep := keep
  flank_nonnegative := by
    intro i j ne
    rw [add_zero]
    exact BudgetPlaces.alpha_nonneg_nonarch v.1 (PhysicalLabels.nonarch v)
      (left_ne_zero_of_mul_eq_one (circle i)) (left_ne_zero_of_mul_eq_one (circle j))
      ((direction_inj inj).ne ne)
  direct_bound := by
    intro i j s h
    have e : neighborDirection b z i-neighborDirection b z j=z i-z j := by unfold neighborDirection; ring
    rw [e,add_zero]; exact h
  reciprocal_bound := by
    intro i j s h
    rw [reciprocal_value circle,reciprocal_value circle,sub_sub_sub_cancel_right,add_zero]
    exact h
  integrable := fun i j _ => positive_integrable hf.measurable (measurable_thresholdTail ..)
    (measurableSet_le measurable_const (measurable_neg.exp))
    (measurableSet_le measurable_const measurable_id.exp) (meas i j)

end
end PlanarUnitDistances.Flanks
