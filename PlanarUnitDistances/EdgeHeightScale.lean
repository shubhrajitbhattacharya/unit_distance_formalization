import PlanarUnitDistances.HeightTransfer
import PlanarUnitDistances.ThresholdProfiles

namespace PlanarUnitDistances.EdgeHeightScale
open MeasureTheory Set Real Finset NumberField
open OAI.PlanarUnitDistances.ThresholdProfiles
noncomputable section

variable {E : Type*} [Fintype E] {K : Type*} [Field K] [NumberField K]

/-- The threshold coordinate is minus the local logarithm of the unit direction. -/
def threshold (v : AbsoluteValue K ℝ) (d : E → K) (e : E) := -log (v (d e))

omit [NumberField K] in
private lemma expected_local_height (p : E → ℝ) (hs : ∑ e, p e = 1)
    (d : E → K) (hd : ∀ e, d e ≠ 0) (v : AbsoluteValue K ℝ) {l u : ℝ}
    (hl : ∀ e, l ≤ threshold v d e) (hu : ∀ e, threshold v d e ≤ u) :
    (∑ x : E × E, (p x.1 * p x.2) * log⁺ (v (d x.1 / d x.2))) =
    ∫ s in Icc l u, frequency p (threshold v d) s * (1-frequency p (threshold v d) s) := by
  classical
  have split (e f : E) : |threshold v d e - threshold v d f| =
      log⁺ (v (d e / d f)) + log⁺ (v (d f / d e)) := by
    have h1 := (v.pos (hd e)).ne'
    have h2 := (v.pos (hd f)).ne'
    simp only [threshold, map_div₀,← Real.half_mul_log_add_log_abs,log_div h1 h2,log_div h2 h1]
    rw [show -log (v (d e))- -log (v (d f))= -(log (v (d e))-log (v (d f))) by ring,
      abs_neg, abs_sub_comm (log (v (d f)))]
    ring
  have rev : (∑ e, ∑ f, p e*p f*log⁺ (v (d f/d e))) =
      ∑ e, ∑ f, p e*p f*log⁺ (v (d e/d f)) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro e _
    apply sum_congr rfl
    intro f _
    rw [mul_comm (p f) (p e)]
  have h := expected_distance_identity p (threshold v d) hs hl hu
  simp only [split,mul_add,sum_add_distrib,rev] at h
  rw [Fintype.sum_prod_type]
  linarith

/-- Sum place integrals in the absolute-height normalization. The finite-place
absolute value already incorporates the residue degree. -/
def placeSum (I : AbsoluteValue K ℝ → ℝ) : ℝ :=
  ((∑ v : InfinitePlace K, (v.mult : ℝ)*I v.val) + ∑ᶠ v : FinitePlace K, I v.val) /
    (Module.finrank ℚ K : ℝ)

def varianceIntegral (p : E → ℝ) (d : E → K) (l u : AbsoluteValue K ℝ → ℝ)
    (v : AbsoluteValue K ℝ) :=
  ∫ s in Icc (l v) (u v), frequency p (threshold v d) s * (1-frequency p (threshold v d) s)

def minorityIntegral (p : E → ℝ) (d : E → K) (l u : AbsoluteValue K ℝ → ℝ)
    (v : AbsoluteValue K ℝ) := ∫ s in Icc (l v) (u v), minority p (threshold v d) s

theorem expected_height_eq_integral (p : E → ℝ) (hs : ∑ e,p e = 1)
    (d : E → K) (hd : ∀ e, d e ≠ 0) (l u : AbsoluteValue K ℝ → ℝ)
    (hl : ∀ v e, l v ≤ threshold v d e) (hu : ∀ v e, threshold v d e ≤ u v) :
    (∑ e, ∑ f, p e*p f*weilHeight (d e/d f)) = placeSum (varianceIntegral p d l u) := by
  rw [← Fintype.sum_prod_type (fun x : E × E => p x.1*p x.2*weilHeight (d x.1/d x.2))]
  rw [HeightTransfer.weighted_height_identity (fun x : E × E => p x.1*p x.2) (fun x => d x.1/d x.2)]
  unfold placeSum varianceIntegral
  simp only [InfinitePlace.coe_apply, FinitePlace.coe_apply,
    expected_local_height p hs d hd _ (hl _) (hu _)]

theorem expected_height_le_scale (p : E → ℝ) (hp : ∀ e, 0 ≤ p e) (hs : ∑ e,p e = 1)
    (d : E → K) (hd : ∀ e, d e ≠ 0) (l u : AbsoluteValue K ℝ → ℝ)
    (hl : ∀ v e, l v ≤ threshold v d e) (hu : ∀ v e, threshold v d e ≤ u v) :
    (∑ e, ∑ f, p e*p f*weilHeight (d e/d f)) ≤ placeSum (minorityIntegral p d l u) := by
  have local_bound (v : AbsoluteValue K ℝ) : varianceIntegral p d l u v ≤ minorityIntegral p d l u v := by
    have h := expected_distance_le p (threshold v d) hp hs (hl v) (hu v)
    rw [expected_distance_identity p (threshold v d) hs (hl v) (hu v)] at h
    exact le_of_mul_le_mul_left h (by norm_num)
  have finT (e : E) : Function.HasFiniteSupport (fun v : FinitePlace K => threshold v.val d e) := by
    apply (FinitePlace.hasFiniteMulSupport (hd e)).subset
    intro v hv
    change v (d e) ≠ 1
    intro he
    apply hv
    change -log (v (d e)) = 0
    simp [he]
  have finMinor : Function.HasFiniteSupport (fun v : FinitePlace K => minorityIntegral p d l u v.val) :=
    finiteSupport_minorIntegral p hs (fun e (v : FinitePlace K) => threshold v.val d e) finT
      (fun v => l v.val) (fun v => u v.val)
  have finVar : Function.HasFiniteSupport (fun v : FinitePlace K => varianceIntegral p d l u v.val) := by
    apply finiteSupport_profile (fun e (v : FinitePlace K) => threshold v.val d e) finT
      (fun v a => ∫ s in Icc (l v.val) (u v.val), frequency p a s * (1-frequency p a s))
    intro v
    have zeroAt (s : ℝ) : frequency p (fun _ => 0) s * (1-frequency p (fun _ => 0) s) = 0 := by
      simp only [frequency,← sum_mul,hs,one_mul,bit]
      split <;> norm_num
    simp only [zeroAt,integral_zero]
  rw [expected_height_eq_integral p hs d hd l u hl hu]
  unfold placeSum
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact add_le_add (sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (local_bound v.val) (Nat.cast_nonneg _))
    (finsum_le_finsum' finVar finMinor fun v => local_bound v.val)

/-- The reference direction is selected among edges of positive probability. -/
theorem exists_reference_edge (p : E → ℝ) (hp : ∀ e, 0 ≤ p e) (hs : ∑ e,p e = 1)
    (d : E → K) (hd : ∀ e, d e ≠ 0) (l u : AbsoluteValue K ℝ → ℝ)
    (hl : ∀ v e, l v ≤ threshold v d e) (hu : ∀ v e, threshold v d e ≤ u v) :
    ∃ f, 0 < p f ∧ (∑ e, p e * weilHeight (d e/d f)) ≤ placeSum (minorityIntegral p d l u) := by
  classical
  let S := placeSum (minorityIntegral p d l u)
  let F (f : E) := ∑ e, p e * weilHeight (d e/d f)
  have hav : (∑ f, p f * F f) ≤ S := by
    have h := expected_height_le_scale p hp hs d hd l u hl hu
    change _ ≤ S at h
    refine le_trans (le_of_eq ?_) h
    simp only [F,mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro e _
    apply sum_congr rfl
    intro f _
    ring
  obtain ⟨i,_,hi⟩ : ∃ i ∈ univ, 0 < p i := by
    by_contra! hh
    have z : ∀ i, p i = 0 := fun i => le_antisymm (hh i (mem_univ i)) (hp i)
    simp [z] at hs
  by_contra! hb
  have strict : (∑ f, p f * S) < ∑ f, p f * F f := by
    apply sum_lt_sum
    · intro f _
      by_cases hf : 0 < p f
      · exact mul_le_mul_of_nonneg_left (hb f hf).le (hp f)
      · simp [le_antisymm (le_of_not_gt hf) (hp f)]
    · exact ⟨i,mem_univ _,mul_lt_mul_of_pos_left (hb i hi) hi⟩
  rw [← sum_mul,hs,one_mul] at strict
  exact (not_lt_of_ge hav) strict

end
end PlanarUnitDistances.EdgeHeightScale
