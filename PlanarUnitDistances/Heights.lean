import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic

namespace PlanarUnitDistances
open Height NumberField Real
open scoped BigOperators
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Mathlib uses the relative height in K. Divide by [K:ℚ] to obtain the absolute logarithmic height. In particular each complex place has weight two before division. -/
def weilHeight (x : K) : ℝ := logHeight₁ x / (Module.finrank ℚ K : ℝ)

private theorem degree_pos : 0 < (Module.finrank ℚ K : ℝ) := by
  exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)

theorem weilHeight_nonneg (x : K) : 0 ≤ weilHeight x :=
  div_nonneg (zero_le_logHeight₁ _) (Nat.cast_nonneg _)

@[simp] theorem weilHeight_one : weilHeight (1 : K) = 0 := by simp [weilHeight]


@[simp] theorem weilHeight_inv (x : K) : weilHeight x⁻¹ = weilHeight x := by
  simp [weilHeight, logHeight₁_inv]

theorem weilHeight_mul (x y : K) : weilHeight (x*y) ≤ weilHeight x + weilHeight y := by
  unfold weilHeight
  rw [← add_div]
  gcongr
  exact logHeight₁_mul_le x y

theorem weilHeight_sub (x y : K) : weilHeight (x-y) ≤ weilHeight x + weilHeight y + log 2 := by
  have h := logHeight₁_sub_le x y
  rw [NumberField.totalWeight_eq_finrank] at h
  unfold weilHeight
  rw [← add_div, div_add' _ _ _ (ne_of_gt (degree_pos (K := K)))]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  linarith

theorem circle_residual_height (z w a b : K) :
    weilHeight ((z-a)*(w-b)-1) ≤
      weilHeight z + weilHeight w + weilHeight a + weilHeight b + 3*log 2 := by
  have h := weilHeight_sub ((z-a)*(w-b)) 1
  rw [weilHeight_one] at h
  linarith [weilHeight_mul (z-a) (w-b), weilHeight_sub z a, weilHeight_sub w b]

/-- The random embedding is uniform on individual complex embeddings, including
both members of a conjugate pair. No choice of Galois closure is necessary. -/
theorem average_embedding_posLog_le_height (x : K) :
    (∑ φ : K →+* ℂ, log⁺ ‖φ x‖) / (Module.finrank ℚ K : ℝ) ≤ weilHeight x := by
  classical
  unfold weilHeight
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [NumberField.logHeight₁_eq]
  have harch : (∑ φ : K →+* ℂ, log⁺ ‖φ x‖) =
      ∑ v : InfinitePlace K, (v.mult : ℝ) * log⁺ (v x) := by
    rw [← Finset.univ.sum_fiberwise (fun φ : K →+* ℂ => InfinitePlace.mk φ)]
    apply Finset.sum_congr rfl
    intro v _
    calc
      _ = ∑ _φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = v),
            log⁺ (v x) := by
        apply Finset.sum_congr rfl
        intro φ hφ
        rw [← (Finset.mem_filter.mp hφ).2]
        rfl
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, InfinitePlace.card_filter_mk_eq]
  rw [harch]
  exact le_add_of_nonneg_right (finsum_nonneg (fun _ => Real.posLog_nonneg))

/-- If a nonzero residual is tiny at an embedding, its inverse pays for it
in the normalized height. The bound uses the *fraction* of all embeddings. -/
theorem small_embedding_fraction {x : K} (hx : x ≠ 0) {s : ℝ} (hs : 0 < s) :
    let E := Finset.univ.filter fun φ : K →+* ℂ => ‖φ x‖ ≤ exp (-s)
    (E.card : ℝ) / (Module.finrank ℚ K : ℝ) ≤ weilHeight x / s := by
  classical
  let E := Finset.univ.filter fun φ : K →+* ℂ => ‖φ x‖ ≤ exp (-s)
  have hnorm (φ : K →+* ℂ) (hφ : φ ∈ E) : s ≤ log⁺ ‖φ x⁻¹‖ := by
    have hpos : 0 < ‖φ x‖ := norm_pos_iff.mpr ((map_ne_zero φ).mpr hx)
    have hlog := log_le_log hpos (Finset.mem_filter.mp hφ).2
    rw [log_exp] at hlog
    rw [map_inv₀, norm_inv, Real.posLog_apply, log_inv]
    exact le_max_of_le_right (by linarith)
  have hsum : (E.card : ℝ)*s ≤ ∑ φ : K →+* ℂ, log⁺ ‖φ x⁻¹‖ := by
    calc
      _ = ∑ _φ ∈ E, s := by simp
      _ ≤ ∑ φ ∈ E, log⁺ ‖φ x⁻¹‖ := Finset.sum_le_sum hnorm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Real.posLog_nonneg)
  change (E.card : ℝ) / _ ≤ _
  rw [le_div_iff₀ hs, div_mul_eq_mul_div]
  exact ((div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)).trans
    (average_embedding_posLog_le_height x⁻¹)).trans_eq (weilHeight_inv x)

end
end PlanarUnitDistances
