import PlanarUnitDistances.MeasuredSlots
import PlanarUnitDistances.MeasurableFlank
import PlanarUnitDistances.ThresholdInterval

namespace PlanarUnitDistances.Flanks
open Set Real MeasureTheory OAI.PlanarUnitDistances Competition.IncidencePiece
open scoped Classical
noncomputable section
variable {I A B : Type*}

/-- A full observed slot at a single place. Endpoints of the common and
balanced intervals need no exceptional convention. Both thresholds of the
sampled pair belong to the prescribed physical interval. -/
theorem integrated_observedSlot (lo hi ε : ℝ) (cut : ε≤1/2) (f g : ℝ → ℝ)
    (good : ℝ → Prop) (level base : ℝ → A×B) (Y : ℝ → I → A×B) (Z : I → ℝ) (i j : I)
    (iwin : Z i∈Icc lo hi) (jwin : Z j∈Icc lo hi) :
    let r := fun v => decide (f v≤1/2)
    let bits := fun v k => decide (v<Z k)
    let selected := fun v => good v ∧ RareScore.exceptional (r v) (level v) (base v)
    let F := positive lo hi ε (Z i) (Z j) f g
      (fun v => (Y v i).1=(Y v j).1) (fun v => (Y v i).2=(Y v j).2) selected
    Integrable F →
      (∫s in Icc lo hi,observedSlot (ε ≤ min (f s) (1-f s)) (good s) (r s) (level s) (base s)
        (g s) (bits s) (Y s) i j) = (∫s,F s)-|Z i-Z j| := by
  intro r bits selected F hF
  have pm (x : ℝ) : Measurable (thresholdBit x) := Measurable.ite measurableSet_Iio measurable_const measurable_const
  have norm (s : ℝ) : ‖|thresholdBit (Z i) s-thresholdBit (Z j) s|‖≤1 := by
    by_cases a : s<Z i <;> by_cases b : s<Z j <;> norm_num [thresholdBit,a,b]
  have hm : IntegrableOn (fun s => |thresholdBit (Z i) s-thresholdBit (Z j) s|) (Icc lo hi) :=
    IntegrableOn.of_bound (measure_Icc_lt_top (μ:=volume)) (((pm _).sub (pm _)).abs.aestronglyMeasurable)
      1 (Filter.Eventually.of_forall norm)
  have support (s : ℝ) (h : s∉Icc lo hi) : F s=0 := by
    have hc : s∉commonRegion lo hi ε f := fun hh => h hh.1
    simp [F,positive,rarePositive,commonPositive,h,hc]
  have extend : (∫s in Icc lo hi,F s) = ∫s,F s := by
    rw [←integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun s => by
      by_cases h : s∈Icc lo hi <;> simp [Set.indicator,h,support])
  calc
    _ = ∫s in Icc lo hi,F s-|thresholdBit (Z i) s-thresholdBit (Z j) s| := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      have point := observedSlot_eq lo hi ε s hs cut f g good level base Y Z i j
      have ex : RareScore.ind (bits s i≠bits s j)=|thresholdBit (Z i) s-thresholdBit (Z j) s| := by
        by_cases a : s<Z i <;> by_cases b : s<Z j <;> norm_num [RareScore.ind,bits,thresholdBit,a,b]
      exact point.trans (congrArg (fun a => F s-a) ex)
    _ = _ := by rw [integral_sub hF.integrableOn hm,extend,
      (threshold_difference iwin.1 jwin.1 iwin.2 jwin.2).2]

end
end PlanarUnitDistances.Flanks
