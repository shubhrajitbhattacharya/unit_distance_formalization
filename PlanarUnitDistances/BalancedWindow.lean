import PlanarUnitDistances.BalancedFlank

namespace PlanarUnitDistances.Flanks
open Set Finset Real MeasureTheory
open scoped Classical
noncomputable section

def commonRegion (lo hi ε : ℝ) (f : ℝ → ℝ) := {s | s∈Icc lo hi ∧ ε≤f s ∧ f s≤1-ε}
def balancedRegion (lo hi ε δ : ℝ) (f g : ℝ → ℝ) :=
  {s | s∈commonRegion lo hi ε f ∧ |g s-1/2|≤δ}

/-- A balanced window may be open at either end, a singleton, or empty.
Its endpoints suffice for two different uses: closed containment for matching
events and open containment for the conditional probability estimate. -/
theorem exists_balanced_window (lo hi ε δ : ℝ) {f g : ℝ → ℝ} (hf : Antitone f) (hg : Antitone g) :
    ∃ l r : ℝ, balancedRegion lo hi ε δ f g ⊆ Icc l r ∧ Ioo l r ⊆ balancedRegion lo hi ε δ f g := by
  let J := balancedRegion lo hi ε δ f g
  by_cases hj : J.Nonempty
  · have hL : BddBelow J := ⟨lo,fun _ h => h.1.1.1⟩
    have hU : BddAbove J := ⟨hi,fun _ h => h.1.1.2⟩
    refine ⟨sInf J,sSup J,fun _ h => ⟨csInf_le hL h,le_csSup hU h⟩,?_⟩
    intro s hs
    obtain ⟨a,ha,has⟩ := exists_lt_of_csInf_lt hj hs.1
    obtain ⟨b,hb,hsb⟩ := exists_lt_of_lt_csSup hj hs.2
    exact ⟨⟨⟨ha.1.1.1.trans has.le,hsb.le.trans hb.1.1.2⟩,
      hb.1.2.1.trans (hf hsb.le),(hf has.le).trans ha.1.2.2⟩,
      abs_le.mpr ⟨(abs_le.mp hb.2).1.trans (sub_le_sub_right (hg hsb.le) _),
        (sub_le_sub_right (hg has.le) _).trans (abs_le.mp ha.2).2⟩⟩
  · refine ⟨1,0,fun s hs => (hj ⟨s,hs⟩).elim,fun s hs => ?_⟩
    exfalso
    linarith [hs.1,hs.2]

lemma tail_antitone {X : Type*} [Fintype X] (μ Z : X → ℝ) (hμ : ∀x,0≤μ x) :
    Antitone (thresholdTail μ Z) := by
  intro l r hlr
  apply sum_le_sum
  intro x _
  by_cases h : r<Z x
  · simp [h,hlr.trans_lt h]
  · simp only [if_neg h]
    split <;> simp [hμ]

lemma tail_bounds {X : Type*} [Fintype X] (μ Z : X → ℝ) (hμ : ∀x,0≤μ x) (total : ∑x,μ x=1) (s : ℝ) :
    0≤thresholdTail μ Z s ∧ thresholdTail μ Z s≤1 := by
  constructor
  · exact sum_nonneg (fun x _ => by split_ifs; exact hμ x; exact le_rfl)
  · rw [←total]
    apply sum_le_sum
    intro x _; split_ifs; exact le_rfl; exact hμ x

/-- The interval and the precise 1/15 correction are simultaneously available
for the actual global and conditional tails, including atoms at endpoints. -/
theorem finite_balanced_window {X : Type*} [Fintype X] (μ Z : X → ℝ)
    (hμ : ∀x,0≤μ x) (total : ∑x,μ x=1) (lo hi ε : ℝ) {f : ℝ → ℝ} (hf : Antitone f) :
    ∃ l r : ℝ, balancedRegion lo hi ε (1/sqrt 24) f (thresholdTail μ Z) ⊆ Icc l r ∧
      Ioo l r ⊆ balancedRegion lo hi ε (1/sqrt 24) f (thresholdTail μ Z) ∧
      (1/6:ℝ)*max 0 (r-l)*(∑x,∑y,if Z x∈Ioo l r ∧ Z y∈Ioo l r then μ x*μ y else 0) ≤
      (1/15:ℝ)*∫s in commonRegion lo hi ε f,2*thresholdTail μ Z s*(1-thresholdTail μ Z s) := by
  obtain ⟨l,r,hc,hi'⟩ := exists_balanced_window lo hi ε (1/sqrt 24) hf (tail_antitone μ Z hμ)
  refine ⟨l,r,hc,hi', (balanced_window_pair_charge μ Z hμ l r (fun s hs => (hi' hs).2)).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hm : Measurable (thresholdTail μ Z) :=
    Finset.measurable_fun_sum _ (fun x _ => Measurable.ite measurableSet_Iio measurable_const measurable_const)
  have hb (s : ℝ) := tail_bounds μ Z hμ total s
  have hn (s : ℝ) : 0≤2*thresholdTail μ Z s*(1-thresholdTail μ Z s) :=
    mul_nonneg (mul_nonneg (by norm_num) (hb s).1) (sub_nonneg.mpr (hb s).2)
  have hsubset : commonRegion lo hi ε f ⊆ Icc lo hi := fun _ h => h.1
  have hfin := (measure_mono (μ:=volume) hsubset).trans_lt (measure_Icc_lt_top (μ:=volume))
  have hint := IntegrableOn.of_bound (f:=fun s => 2*thresholdTail μ Z s*(1-thresholdTail μ Z s)) hfin
    ((measurable_const.mul hm).mul (measurable_const.sub hm)).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hn s)]
      nlinarith [sq_nonneg (thresholdTail μ Z s-1/2)])
  exact setIntegral_mono_set hint (Filter.Eventually.of_forall hn)
    (Filter.Eventually.of_forall fun _ hs => (hi' hs).1)

end
end PlanarUnitDistances.Flanks
