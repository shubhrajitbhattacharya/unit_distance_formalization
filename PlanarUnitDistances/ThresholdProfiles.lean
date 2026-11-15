import Mathlib

/- Adapted from OpenAI math, UnitDistances/Levels.lean, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, Apache-2.0. -/
namespace OAI
namespace PlanarUnitDistances.ThresholdProfiles
open MeasureTheory Set
open scoped BigOperators
noncomputable section

def bit (a s : ℝ) : ℝ := if s < a then 1 else 0

lemma bit_nonneg (a s : ℝ) : 0 ≤ bit a s := by unfold bit; split <;> norm_num
lemma bit_le_one (a s : ℝ) : bit a s ≤ 1 := by unfold bit; split <;> norm_num
lemma bit_measurable (a : ℝ) : Measurable (bit a) :=
  Measurable.ite measurableSet_Iio measurable_const measurable_const

lemma bit_integrableOn (a l u : ℝ) : IntegrableOn (bit a) (Icc l u) := by
  have he : bit a = (Iio a).indicator (fun _ => (1 : ℝ)) := by
    funext s; simp [bit,Set.indicator]
  rw [he]
  exact (show Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Icc l u))
    from continuous_const.integrableOn_Icc).indicator measurableSet_Iio

lemma abs_bit_sub_eq (a b s : ℝ) :
    |bit a s - bit b s| = (Ico (min a b) (max a b)).indicator (fun _ => (1 : ℝ)) s := by
  by_cases ha : s < a <;> by_cases hb : s < b <;>
    simp [bit,ha,hb,Set.indicator,mem_Ico]

lemma bit_sub_integral {l u a b : ℝ} (hla : l ≤ a) (hua : a ≤ u)
    (hlb : l ≤ b) (hub : b ≤ u) :
    ∫ s in Icc l u, |bit a s - bit b s| = |a-b| := by
  simp_rw [abs_bit_sub_eq]
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ico]
  rw [measureReal_restrict_apply measurableSet_Ico]
  have hsub : Ico (min a b) (max a b) ⊆ Icc l u := by
    intro s hs
    exact ⟨(le_min hla hlb).trans hs.1, hs.2.le.trans (max_le hua hub)⟩
  rw [inter_eq_left.mpr hsub,Real.volume_real_Ico]
  simp [smul_eq_mul,max_sub_min_eq_abs,abs_sub_comm]

lemma bit_mismatch (a b s : ℝ) :
    |bit a s - bit b s| = bit a s + bit b s - 2*bit a s*bit b s := by
  unfold bit
  split <;> split <;> norm_num

variable {E : Type*} [Fintype E]

def frequency (p : E → ℝ) (a : E → ℝ) (s : ℝ) : ℝ := ∑ e, p e * bit (a e) s

def minority (p : E → ℝ) (a : E → ℝ) (s : ℝ) : ℝ :=
  min (frequency p a s) (1-frequency p a s)

lemma frequency_nonneg (p : E → ℝ) (hp : ∀ e, 0 ≤ p e) (a : E → ℝ) (s : ℝ) :
    0 ≤ frequency p a s := Finset.sum_nonneg fun e _ => mul_nonneg (hp e) (bit_nonneg _ _)

lemma frequency_le_one (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hs : ∑ e, p e = 1) (a : E → ℝ) (s : ℝ) : frequency p a s ≤ 1 := by
  unfold frequency
  calc
    _ ≤ ∑ e, p e := Finset.sum_le_sum fun e _ => mul_le_of_le_one_right (hp e) (bit_le_one _ _)
    _ = 1 := hs

lemma frequency_measurable (p : E → ℝ) (a : E → ℝ) : Measurable (frequency p a) := by
  unfold frequency
  exact Finset.measurable_sum Finset.univ fun e _ =>
    measurable_const.mul (bit_measurable (a e))

lemma minority_integrableOn (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hs : ∑ e, p e = 1) (a : E → ℝ) (l u : ℝ) :
    IntegrableOn (minority p a) (Icc l u) := by
  have hm : Measurable (minority p a) :=
    (frequency_measurable p a).min (measurable_const.sub (frequency_measurable p a))
  apply Integrable.of_bound hm.aestronglyMeasurable (1 : ℝ)
  filter_upwards [] with s
  change |min (frequency p a s) (1-frequency p a s)| ≤ 1
  rw [abs_of_nonneg (le_min (frequency_nonneg p hp a s)
    (sub_nonneg.mpr (frequency_le_one p hp hs a s)))]
  exact (min_le_left _ _).trans (frequency_le_one p hp hs a s)

lemma independent_mismatch (p : E → ℝ) (hs : ∑ e, p e = 1) (a : E → ℝ) (s : ℝ) :
    (∑ e, ∑ f, p e*p f*|bit (a e) s-bit (a f) s|) =
      2*frequency p a s*(1-frequency p a s) := by
  simp_rw [bit_mismatch]
  simp_rw [mul_sub,mul_add]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  have h₁ : (∑ e, ∑ f, p e*p f*bit (a e) s) = frequency p a s := by
    simp_rw [mul_right_comm (p _) (p _) (bit _ _),← Finset.mul_sum,hs,mul_one]
    rfl
  have h₂ : (∑ e, ∑ f, p e*p f*bit (a f) s) = frequency p a s := by
    simp_rw [mul_assoc,← Finset.mul_sum,← Finset.sum_mul,hs,one_mul]
    rfl
  have h₃ : (∑ e, ∑ f, p e*p f*(2*bit (a e) s*bit (a f) s)) =
      2*frequency p a s*frequency p a s := by
    have he (e f : E) : p e*p f*(2*bit (a e) s*bit (a f) s) =
        (2*(p e*bit (a e) s))*(p f*bit (a f) s) := by ring
    simp_rw [he,← Finset.mul_sum,← Finset.sum_mul]
    unfold frequency
    rw [← Finset.mul_sum]
  rw [h₁,h₂,h₃]
  ring

lemma mismatch_le_twice_minority (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hs : ∑ e, p e = 1) (a : E → ℝ) (s : ℝ) :
    (∑ e, ∑ f, p e*p f*|bit (a e) s-bit (a f) s|) ≤ 2*minority p a s := by
  rw [independent_mismatch p hs a s,minority,mul_min_of_nonneg _ _ (by norm_num)]
  have h0 := frequency_nonneg p hp a s
  have h1 := frequency_le_one p hp hs a s
  apply le_min <;> nlinarith [sq_nonneg (frequency p a s),sq_nonneg (1-frequency p a s)]

lemma pair_integrableOn (c a b l u : ℝ) :
    IntegrableOn (fun s => c * |bit a s-bit b s|) (Icc l u) :=
  ((bit_integrableOn a l u).sub (bit_integrableOn b l u)).abs.const_mul c

lemma mismatch_integrableOn (p a : E → ℝ) (l u : ℝ) :
    IntegrableOn (fun s => ∑ e, ∑ f, p e*p f*|bit (a e) s-bit (a f) s|) (Icc l u) := by
  exact integrable_finsetSum Finset.univ fun e _ =>
    integrable_finsetSum Finset.univ fun f _ => pair_integrableOn _ _ _ _ _

lemma integrated_mismatch (p a : E → ℝ) {l u : ℝ}
    (hla : ∀ e, l ≤ a e) (hua : ∀ e, a e ≤ u) :
    (∫ s in Icc l u, ∑ e, ∑ f, p e*p f*|bit (a e) s-bit (a f) s|) =
      ∑ e, ∑ f, p e*p f*|a e-a f| := by
  rw [integral_finsetSum Finset.univ (fun e _ =>
    integrable_finsetSum Finset.univ fun f _ => pair_integrableOn _ _ _ _ _)]
  apply Finset.sum_congr rfl
  intro e _
  rw [integral_finsetSum Finset.univ (fun f _ => pair_integrableOn _ _ _ _ _)]
  apply Finset.sum_congr rfl
  intro f _
  rw [integral_const_mul,bit_sub_integral (hla e) (hua e) (hla f) (hua f)]

lemma expected_distance_identity (p a : E → ℝ) (hs : ∑ e, p e = 1) {l u : ℝ}
    (hla : ∀ e, l ≤ a e) (hua : ∀ e, a e ≤ u) :
    (∑ e, ∑ f, p e*p f*|a e-a f|) =
      2 * ∫ s in Icc l u, frequency p a s * (1-frequency p a s) := by
  rw [← integrated_mismatch p a hla hua]
  simp_rw [independent_mismatch p hs,mul_assoc (2 : ℝ)]
  exact integral_const_mul _ _

lemma expected_distance_le (p a : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    (hs : ∑ e, p e = 1) {l u : ℝ} (hla : ∀ e, l ≤ a e) (hua : ∀ e, a e ≤ u) :
    (∑ e, ∑ f, p e*p f*|a e-a f|) ≤ 2 * ∫ s in Icc l u, minority p a s := by
  rw [← integrated_mismatch p a hla hua,← integral_const_mul]
  exact integral_mono (mismatch_integrableOn p a l u)
    ((minority_integrableOn p hp hs a l u).const_mul 2)
    (mismatch_le_twice_minority p hp hs a)

lemma minority_of_constant (p : E → ℝ) (hs : ∑ e, p e = 1) (c s : ℝ) :
    minority p (fun _ => c) s = 0 := by
  simp only [minority,frequency,← Finset.sum_mul,hs,one_mul]
  unfold bit
  split <;> norm_num

end
end PlanarUnitDistances.ThresholdProfiles

namespace PlanarUnitDistances.ThresholdProfiles
open MeasureTheory Set
open scoped BigOperators
noncomputable section

lemma finiteSupport_profile {V E : Type*} [Finite E] (a : E → V → ℝ)
    (ha : ∀ e, Function.HasFiniteSupport (a e)) (F : V → (E → ℝ) → ℝ)
    (hF : ∀ v, F v (fun _ => 0) = 0) :
    Function.HasFiniteSupport (fun v => F v (fun e => a e v)) := by
  classical
  apply (Set.finite_iUnion fun e => ha e).subset
  intro v hv
  by_contra hn
  have hz : (fun e => a e v) = fun _ => 0 := by
    funext e
    by_contra he
    exact hn (Set.mem_iUnion.mpr ⟨e,he⟩)
  exact hv (by change F v (fun e => a e v) = 0; rw [hz,hF])

lemma finiteSupport_minorIntegral {V E : Type*} [Fintype E]
    (p : E → ℝ) (hs : ∑ e, p e = 1) (a : E → V → ℝ)
    (ha : ∀ e, Function.HasFiniteSupport (a e)) (l u : V → ℝ) :
    Function.HasFiniteSupport (fun v => ∫ s in Icc (l v) (u v),
      minority p (fun e => a e v) s) := by
  apply finiteSupport_profile a ha (fun v a => ∫ s in Icc (l v) (u v), minority p a s)
  intro v
  simp only [minority_of_constant p hs,integral_zero]

end
end PlanarUnitDistances.ThresholdProfiles
end OAI
