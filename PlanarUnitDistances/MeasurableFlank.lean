import PlanarUnitDistances.ConditionalFlanks

namespace PlanarUnitDistances.Flanks
open Set MeasureTheory Real Finset OAI.PlanarUnitDistances
open scoped Classical
noncomputable section

/-- Measurable choices of the retained rare levels and coordinate matches
give the integrability needed in the local flank theorem on every bounded
level interval, with no regularity assumed of the rare-label rule. -/
theorem positive_integrable {lo hi ε b b' : ℝ} {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) {z w k : ℝ → Prop}
    (hz : MeasurableSet {s | z s}) (hw : MeasurableSet {s | w s}) (hk : MeasurableSet {s | k s}) :
    Integrable (positive lo hi ε b b' f g z w k) := by
  have ho : MeasurableSet {s | bothOne b b' w s} := measurableSet_Iio.inter (measurableSet_Iio.inter hw)
  have h₀ : MeasurableSet {s | bothZero b b' z s} := measurableSet_Ici.inter (measurableSet_Ici.inter hz)
  have cset : MeasurableSet (commonRegion lo hi ε f) := measurableSet_Icc.inter
    ((measurableSet_le measurable_const hf).inter (measurableSet_le hf measurable_const))
  have box : MeasurableSet {s | s∈commonRegion lo hi ε f ∧ (bothOne b b' w s ∨ bothZero b b' z s)} :=
    cset.inter (ho.union h₀)
  have rb : MeasurableSet {s | (s∈Icc lo hi ∧ k s ∧ f s<ε ∧ bothOne b b' w s) ∨
      (s∈Icc lo hi ∧ k s ∧ 1-ε<f s ∧ bothZero b b' z s)} :=
    (measurableSet_Icc.inter (hk.inter ((measurableSet_lt hf measurable_const).inter ho))).union
      (measurableSet_Icc.inter (hk.inter ((measurableSet_lt measurable_const hf).inter h₀)))
  have coeff : Measurable (fun s => StrictCross.coefficient (g s)) := Measurable.ite
    (measurableSet_le ((hg.sub measurable_const).abs) measurable_const) measurable_const measurable_const
  have cm : Measurable (commonPositive lo hi ε b b' f g z w) := Measurable.ite box coeff measurable_const
  have rm : Measurable (rarePositive lo hi ε b b' f z w k) := Measurable.ite rb measurable_const measurable_const
  let p := positive lo hi ε b b' f g z w k
  have pm : Measurable p := rm.add cm
  have normBound (s : ℝ) : ‖p s‖≤4 := by
    dsimp only [p,positive,commonPositive,rarePositive]
    rw [Real.norm_eq_abs]
    split_ifs <;> apply abs_le.mpr <;> constructor <;>
      linarith [StarScore.coefficient_nonneg (g s),StarScore.coefficient_upper (g s)]
  have within : IntegrableOn p (Icc lo hi) := IntegrableOn.of_bound
    (measure_Icc_lt_top (μ:=volume)) pm.aestronglyMeasurable 4 (Filter.Eventually.of_forall normBound)
  have eq : (Icc lo hi).indicator p=p := by
    funext s; by_cases h : s∈Icc lo hi
    · simp [h]
    · have outside : s∉commonRegion lo hi ε f := fun hs => h hs.1
      simp [p,positive,rarePositive,commonPositive,h,outside]
  simpa only [eq] using within.integrable_indicator measurableSet_Icc

theorem measurable_thresholdTail {I : Type*} [Fintype I] (μ Z : I → ℝ) :
    Measurable (thresholdTail μ Z) := Finset.measurable_fun_sum _
    (fun i _ => Measurable.ite measurableSet_Iio measurable_const measurable_const)

end
end PlanarUnitDistances.Flanks
