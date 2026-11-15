import PlanarUnitDistances.ResidualTest
import PlanarUnitDistances.ThreeCenters

/-! # A single-center proof of the bounded-height obstruction

Given the original point, its history resampling and its center are independent.
For distinct original and predicted points at most two centers can pass the
exact circle equation. This avoids the simultaneous three-center experiment.
-/

open Finset Real NumberField
open scoped BigOperators
open scoped Classical

namespace PlanarUnitDistances.BoundedHeight
noncomputable section

/-- Conditional probability of an exact predicted edge against a uniform
neighboring center. The same predicted point is held fixed in the count. -/
theorem single_center {P Q K : Type*} [Field K] [DecidableEq P]
    (centers : P → Finset Q) (zp wp : P → K) (zq wq : Q → K)
    (hzp : Function.Injective zp) (hzq : Function.Injective zq)
    (hedge : ∀ p q, q ∈ centers p → (zp p-zq q)*(wp p-wq q) = 1)
    (p r : P) (d : ℝ) (hd : 0 < d) (hdeg : d ≤ (centers p).card) :
    let hits := (centers p).filter (fun q => (zp r-zq q)*(wp r-wq q) = 1)
    (hits.card : ℝ) / (centers p).card ≤ (if p=r then 1 else 0) + 2/d := by
  classical
  intro hits
  have degpos := hd.trans_le hdeg
  by_cases same : p=r
  · rw [if_pos same]
    have bound : (hits.card : ℝ) / (centers p).card ≤ 1 :=
      (div_le_one degpos).2 (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset ..)))
    linarith [show (0:ℝ) ≤ 2/d by positivity]
  · rw [if_neg same, zero_add]
    have hc := common_centers_le_two hits zq wq hzq.injOn
      (fun he => same (hzp he.symm))
      (fun q hq => hedge p q (Finset.mem_filter.mp hq).1)
      (fun q hq => (Finset.mem_filter.mp hq).2)
    calc
      _ ≤ 2 / ((centers p).card : ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hc) degpos.le
      _ ≤ 2/d := by gcongr

/-- Uniform embeddings where one specified coordinate overflows. -/
theorem overflow_fraction {K : Type*} [Field K] [NumberField K] (x : K) {a : ℝ} (ha : 0 < a) :
    let G := Finset.univ.filter fun φ : K →+* ℂ => exp a < ‖φ x‖
    (G.card : ℝ) / (Module.finrank ℚ K : ℝ) ≤ weilHeight x/a := by
  classical
  intro G
  have pt (φ : K →+* ℂ) (hp : φ ∈ G) : a ≤ log⁺ ‖φ x‖ := by
    have hn := (Finset.mem_filter.mp hp).2
    have hlog := Real.log_le_log (Real.exp_pos a) hn.le
    rw [Real.log_exp] at hlog
    exact hlog.trans (le_max_right _ _)
  have hh : (G.card : ℝ)*a ≤ ∑ φ : K →+* ℂ, log⁺ ‖φ x‖ := calc
    _ = ∑ _φ ∈ G, a := by simp
    _ ≤ ∑ φ ∈ G, log⁺ ‖φ x‖ := Finset.sum_le_sum pt
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G) (fun _ _ _ => Real.posLog_nonneg)
  rw [le_div_iff₀ ha, div_mul_eq_mul_div]
  exact (div_le_div_of_nonneg_right hh (Nat.cast_nonneg _)).trans (average_embedding_posLog_le_height x)

open CircleCells in
/-- Test the two coordinates at an embedding, with automatic acceptance for
an overflowing center and the neighbor-cell rule otherwise. -/
def passes {K P : Type*} [Field K] [NumberField K] (S : Finset P)
    (zp wp : P → K) (x y c d : K) (R : ℝ) (N : ℕ) (hN : 0 < N) (φ : K →+* ℂ) : Prop :=
  R < ‖φ c‖ ∨ R < ‖φ d‖ ∨ code R N hN (φ x) (φ y) ∈ accepted S (φ ∘ zp) (φ ∘ wp) R N hN

open CircleCells in
/-- All overflow cases and the bounded residual on one actual nonedge,
averaged over the same uniform random embedding. -/
theorem false_fraction {K P : Type*} [Field K] [NumberField K]
    (S : Finset P) (zp wp : P → K) (x y c d : K)
    (hedge : ∀ i ∈ S, (zp i-c)*(wp i-d)=1) (hfalse : (x-c)*(y-d) ≠ 1)
    {a s : ℝ} (ha : 0 < a) (hs : 0 < s) {N : ℕ} (hN : 0 < N)
    (hmesh : 8*exp a*width (exp a) N ≤ exp (-s)) :
    let G := Finset.univ.filter (passes S zp wp x y c d (exp a) N hN)
    (G.card : ℝ) / (Module.finrank ℚ K : ℝ) ≤
      (weilHeight x+weilHeight y+weilHeight c+weilHeight d)/a +
      (weilHeight x+weilHeight y+weilHeight c+weilHeight d+3*log 2)/s := by
  classical
  intro G
  let O (t : K) := Finset.univ.filter fun φ : K →+* ℂ => exp a < ‖φ t‖
  let E := Finset.univ.filter fun φ : K →+* ℂ => ‖φ x‖ ≤ exp a ∧ ‖φ y‖ ≤ exp a ∧
    ‖φ c‖ ≤ exp a ∧ ‖φ d‖ ≤ exp a ∧
    code (exp a) N hN (φ x) (φ y) ∈ accepted S (φ ∘ zp) (φ ∘ wp) (exp a) N hN
  have sub : G ⊆ O x ∪ O y ∪ O c ∪ O d ∪ E := by
    intro φ hφ
    simp only [mem_union, G, O, E, Finset.mem_filter, Finset.mem_univ, true_and] at hφ ⊢
    rcases hφ with h | h | h
    · tauto
    · tauto
    by_cases h₁ : ‖φ x‖ ≤ exp a <;> by_cases h₂ : ‖φ y‖ ≤ exp a <;>
      by_cases h₃ : ‖φ c‖ ≤ exp a <;> by_cases h₄ : ‖φ d‖ ≤ exp a <;> grind
  have natbd : G.card ≤ (O x).card+(O y).card+(O c).card+(O d).card+E.card := by
    have hs₀ := Finset.card_le_card sub
    have t₁ := Finset.card_union_le (O x) (O y)
    have t₂ := Finset.card_union_le (O x ∪ O y) (O c)
    have t₃ := Finset.card_union_le (O x ∪ O y ∪ O c) (O d)
    have t₄ := Finset.card_union_le (O x ∪ O y ∪ O c ∪ O d) E
    omega
  have ar := bounded_false_acceptance S zp wp x y c d hedge (sub_ne_zero.mpr hfalse)
    (Real.exp_pos _) hs hN hmesh
  have sumHeight := circle_residual_height x y c d
  have bd := div_le_div_of_nonneg_right (by exact_mod_cast natbd :
      (G.card : ℝ) ≤ (O x).card+(O y).card+(O c).card+(O d).card+E.card)
      (Nat.cast_nonneg (Module.finrank ℚ K) : 0 ≤ (Module.finrank ℚ K : ℝ))
  simp only [add_div] at bd
  change (E.card : ℝ) / _ ≤ _ at ar
  have ov (t : K) : ((O t).card : ℝ) / (Module.finrank ℚ K : ℝ) ≤ weilHeight t / a :=
    overflow_fraction t ha
  have sr := div_le_div_of_nonneg_right sumHeight hs.le
  simp only [add_div]
  simp only [add_div] at sr
  linarith [ov x, ov y, ov c, ov d]



/-- Averaging the false-positive estimate over an arbitrary finite coupling,
independent of the uniform embedding. It suffices to bound the sum of the
four mean coordinate heights under that coupling. -/
theorem false_acceptance_coupling {K P Ω : Type*} [Field K] [NumberField K] [Fintype Ω]
    (mass : Ω → ℝ) (S : Ω → Finset P) (zp wp : P → K) (x y c d : Ω → K)
    (hm : ∀ ω, 0 ≤ mass ω) (htotal : ∑ ω, mass ω = 1)
    (hedge : ∀ ω i, i ∈ S ω → (zp i-c ω)*(wp i-d ω)=1)
    {H a s : ℝ} (ha : 0 < a) (hs : 0 < s) {N : ℕ} (hN : 0 < N)
    (hmesh : 8*exp a*CircleCells.width (exp a) N ≤ exp (-s))
    (hmean : (∑ ω, mass ω * (weilHeight (x ω)+weilHeight (y ω)+weilHeight (c ω)+weilHeight (d ω))) ≤ H) :
    let G := fun ω => Finset.univ.filter (passes (S ω) zp wp (x ω) (y ω) (c ω) (d ω) (exp a) N hN)
    (∑ ω, mass ω * (if (x ω-c ω)*(y ω-d ω) = 1 then 0 else
      ((G ω).card : ℝ) / Module.finrank ℚ K)) ≤ H/a + (H+3*log 2)/s := by
  classical
  intro G
  let ht (ω : Ω) := weilHeight (x ω)+weilHeight (y ω)+weilHeight (c ω)+weilHeight (d ω)
  have nn (ω : Ω) : 0 ≤ ht ω := by
    dsimp [ht]
    linarith only [weilHeight_nonneg (x ω), weilHeight_nonneg (y ω),
      weilHeight_nonneg (c ω), weilHeight_nonneg (d ω)]
  have bound (ω : Ω) : (if (x ω-c ω)*(y ω-d ω) = 1 then (0:ℝ) else
      ((G ω).card : ℝ) / Module.finrank ℚ K) ≤ ht ω/a+(ht ω+3*log 2)/s := by
    split_ifs with h
    · positivity [nn ω, Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]
    · exact false_fraction (S ω) zp wp _ _ _ _ (hedge ω) h ha hs hN hmesh
  have big := Finset.sum_le_sum (s := Finset.univ) (fun ω _ => mul_le_mul_of_nonneg_left (bound ω) (hm ω))
  have split (ω : Ω) : mass ω*(ht ω/a+(ht ω+3*log 2)/s) =
      mass ω * ht ω/a + mass ω * ht ω/s + mass ω*(3*log 2/s) := by ring
  simp only [split, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
    htotal, one_mul] at big
  change (∑ ω, mass ω * ht ω) ≤ H at hmean
  rw [add_div]
  linarith [div_le_div_of_nonneg_right hmean ha.le, div_le_div_of_nonneg_right hmean hs.le]

end
end PlanarUnitDistances.BoundedHeight

