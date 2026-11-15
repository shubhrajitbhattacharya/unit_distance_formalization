import PlanarUnitDistances.SignedRecord
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace PlanarUnitDistances.Competition.IncidencePiece
open Set MeasureTheory
open scoped Classical
noncomputable section

def thresholdBit (n s : ℝ) : ℝ := if s<n then 1 else 0

@[simp] theorem bitValue_decide (s n : ℝ) : bitValue (decide (s<n))=thresholdBit n s := by
  by_cases h : s<n <;> simp [h,bitValue,thresholdBit]

private lemma ordered_threshold {l h a b : ℝ} (lo : l≤a) (ab : a≤b) (hi : b≤h) :
    (∫s in Icc l h,thresholdBit b s-thresholdBit a s)=b-a ∧
    (∫s in Icc l h,|thresholdBit b s-thresholdBit a s|)=b-a := by
  have rep (s : ℝ) : thresholdBit b s-thresholdBit a s=(Ico a b).indicator (fun _ => (1:ℝ)) s := by
    by_cases sa : s<a
    · have sb := lt_of_lt_of_le sa ab
      simp [thresholdBit,Set.indicator,sa,sb,not_le_of_gt sa]
    · by_cases sb : s<b <;> simp [thresholdBit,Set.indicator,sa,sb,le_of_not_gt sa]
  have nn (s : ℝ) : 0≤thresholdBit b s-thresholdBit a s := by
    rw [rep]; exact indicator_nonneg (fun _ _ => zero_le_one) _
  have sub : Ico a b ⊆ Icc l h := fun _ hs => ⟨lo.trans hs.1,hs.2.le.trans hi⟩
  have eq : (∫s in Icc l h,thresholdBit b s-thresholdBit a s)=b-a := by
    simp_rw [rep]; rw [integral_indicator_const (μ:=volume.restrict (Icc l h)) (1:ℝ) measurableSet_Ico,
      measureReal_restrict_apply measurableSet_Ico,inter_eq_left.mpr sub,Real.volume_real_Ico_of_le ab,smul_eq_mul,mul_one]
  exact ⟨eq,by simpa only [abs_of_nonneg (nn _)] using eq⟩

/-- The absolute difference of the two nested threshold bits has the
absolute difference of the thresholds as its integral, including ties. -/
theorem threshold_difference {l h a b : ℝ} (la : l≤a) (lb : l≤b) (ah : a≤h) (bh : b≤h) :
    (∫s in Icc l h,thresholdBit a s-thresholdBit b s)=a-b ∧
    (∫s in Icc l h,|thresholdBit a s-thresholdBit b s|)=|a-b| := by
  rcases le_total b a with ba|ab
  · rw [abs_of_nonneg (sub_nonneg.mpr ba)]
    exact ordered_threshold lb ba ah
  · obtain ⟨sign,unsign⟩ := ordered_threshold la ab bh
    constructor
    · rw [show (fun s => thresholdBit a s-thresholdBit b s)=fun s => -(thresholdBit b s-thresholdBit a s)
        from funext fun s => (neg_sub ..).symm,integral_neg,sign,neg_sub]
    · simp_rw [abs_sub_comm (thresholdBit a _) (thresholdBit b _)]
      rw [abs_sub_comm a b,abs_of_nonneg (sub_nonneg.mpr ab)]; exact unsign

end
end PlanarUnitDistances.Competition.IncidencePiece
