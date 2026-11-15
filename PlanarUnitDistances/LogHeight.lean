import PlanarUnitDistances.Heights

/-! # Absolute logarithmic height and the weighted norm of local logarithms -/

open Real NumberField Height
open scoped BigOperators

namespace PlanarUnitDistances

variable {K : Type*} [Field K] [NumberField K]

private theorem absLog_split (u : ℝ) : |Real.log u| = log⁺ u + log⁺ u⁻¹ := by
  rw [← Real.half_mul_log_add_log_abs, ← Real.half_mul_log_add_log_abs, Real.log_inv, abs_neg]
  ring

private theorem finitePosLog {x : K} (hx : x ≠ 0) :
    (fun v : FinitePlace K => log⁺ (v x)).HasFiniteSupport := by
  apply (FinitePlace.hasFiniteMulSupport hx).subset
  intro v hv
  change log⁺ (v x) ≠ 0 at hv
  change v x ≠ 1
  intro he
  exact hv (by simp [he])

/-- Product formula with Mathlib's normalized finite absolute values.
Complex multiplicity occurs exactly once, as the coefficient of the sum over
infinite places. All finite sums below have genuine finite support. -/
theorem twice_weilHeight_eq_absLog {x : K} (hx : x ≠ 0) :
    2 * weilHeight x =
      ((∑ v : InfinitePlace K, (v.mult : ℝ) * |Real.log (v x)|) +
       ∑ᶠ v : FinitePlace K, |Real.log (v x)|) / Module.finrank ℚ K := by
  have infinite : (∑ v : InfinitePlace K, (v.mult : ℝ) * |Real.log (v x)|) =
      (∑ v : InfinitePlace K, (v.mult : ℝ) * log⁺ (v x)) +
      ∑ v : InfinitePlace K, (v.mult : ℝ) * log⁺ (v x⁻¹) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rw [absLog_split, map_inv₀, mul_add]
  have finite : (∑ᶠ v : FinitePlace K, |Real.log (v x)|) =
      (∑ᶠ v : FinitePlace K, log⁺ (v x)) + ∑ᶠ v : FinitePlace K, log⁺ (v x⁻¹) := by
    rw [← finsum_add_distrib (finitePosLog hx) (finitePosLog (inv_ne_zero hx))]
    apply finsum_congr
    intro v
    rw [absLog_split, map_inv₀]
  unfold weilHeight
  rw [infinite, finite]
  have h := (NumberField.logHeight₁_eq x)
  have hi := NumberField.logHeight₁_eq x⁻¹
  rw [Height.logHeight₁_inv] at hi
  linear_combination ((1 : ℝ) / Module.finrank ℚ K) * (h + hi)


/-- A common finite list of places, represented by a sum type. The finite
component is still an infinite type; the norm below uses exactly its
finitely supported functions. -/
abbrev HeightPlace (K : Type*) [Field K] [NumberField K] := InfinitePlace K ⊕ FinitePlace K

noncomputable def localLog (x : K) : HeightPlace K → ℝ :=
  Sum.elim (fun v => Real.log (v x)) (fun v => Real.log (v x))

/-- Absolute-log sum, normalized by the field degree. -/
noncomputable def placeNorm (u : HeightPlace K → ℝ) : ℝ :=
  ((∑ v : InfinitePlace K, (v.mult : ℝ) * |u (.inl v)|) +
    ∑ᶠ v : FinitePlace K, |u (.inr v)|) / Module.finrank ℚ K

def FiniteAtPrimes (u : HeightPlace K → ℝ) : Prop :=
  (fun v : FinitePlace K => u (.inr v)).HasFiniteSupport

private theorem finiteLog {x : K} (hx : x ≠ 0) : FiniteAtPrimes (localLog x) := by
  apply (FinitePlace.hasFiniteMulSupport hx).subset
  intro v hv
  change Real.log (v x) ≠ 0 at hv
  change v x ≠ 1
  intro he
  exact hv (by simp [he])

private theorem finite_abs {u : HeightPlace K → ℝ} (hu : FiniteAtPrimes u) :
    (fun v : FinitePlace K => |u (.inr v)|).HasFiniteSupport := by
  exact hu.subset (fun v h => by
    change |u (.inr v)| ≠ 0 at h
    exact fun hv => h (by simp [show u (.inr v) = 0 from hv]))

private theorem finite_add {u v : HeightPlace K → ℝ}
    (hu : FiniteAtPrimes u) (hv : FiniteAtPrimes v) : FiniteAtPrimes (u+v) :=
  Function.HasFiniteSupport.fun_add hu hv

private theorem finite_neg {u : HeightPlace K → ℝ} (hu : FiniteAtPrimes u) :
    FiniteAtPrimes (-u) := Function.HasFiniteSupport.fun_neg hu

private theorem placeNorm_add (u v : HeightPlace K → ℝ) (hu : FiniteAtPrimes u)
    (hv : FiniteAtPrimes v) : placeNorm (u+v) ≤ placeNorm u + placeNorm v := by
  have hi := Finset.sum_le_sum (s := Finset.univ)
    (fun a (_ : a ∈ Finset.univ) => mul_le_mul_of_nonneg_left
      (abs_add_le (u (.inl a)) (v (.inl a))) (Nat.cast_nonneg (InfinitePlace.mult a)))
  simp only [mul_add, Finset.sum_add_distrib] at hi
  have hf := finsum_le_finsum' (finite_abs (finite_add hu hv))
    (Function.HasFiniteSupport.fun_add (finite_abs hu) (finite_abs hv))
    (fun a => abs_add_le (u (.inr a)) (v (.inr a)))
  rw [finsum_add_distrib (finite_abs hu) (finite_abs hv)] at hf
  unfold placeNorm
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simp only [Pi.add_apply] at hf ⊢
  linarith

@[simp] private theorem placeNorm_neg (u : HeightPlace K → ℝ) : placeNorm (-u) = placeNorm u := by
  simp [placeNorm]

private theorem localLog_rectangle {a b c d : K} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) : localLog (a*d/(b*c)) = localLog a + localLog d - localLog b - localLog c := by
  funext v
  rcases v with v | v <;>
    simp only [localLog, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Pi.sub_apply,
      map_div₀, map_mul, Real.log_div (mul_ne_zero ((map_ne_zero v).2 ha) ((map_ne_zero v).2 hd))
        (mul_ne_zero ((map_ne_zero v).2 hb) ((map_ne_zero v).2 hc)),
      Real.log_mul ((map_ne_zero v).2 ha) ((map_ne_zero v).2 hd),
      Real.log_mul ((map_ne_zero v).2 hb) ((map_ne_zero v).2 hc)] <;> ring

/-- The concrete height estimate on a four-cycle.
The four units are the four assigned ratio values in row-major order.
One vector is attached to each endpoint; finite prime supports permit genuine
sums, and the same error bound is used on all four incidences. -/
theorem quotient_height_of_endpoint_errors {a b c d : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (P P' R R' : HeightPlace K → ℝ)
    (hP : FiniteAtPrimes P) (hP' : FiniteAtPrimes P')
    (hR : FiniteAtPrimes R) (hR' : FiniteAtPrimes R') (s : ℝ)
    (ea : placeNorm (localLog a - (R-P)) ≤ s)
    (eb : placeNorm (localLog b - (R'-P)) ≤ s)
    (ec : placeNorm (localLog c - (R-P')) ≤ s)
    (ed : placeNorm (localLog d - (R'-P')) ≤ s) :
    weilHeight (a*d/(b*c)) ≤ 2*s := by
  let A := localLog a - (R-P)
  let B := localLog b - (R'-P)
  let C := localLog c - (R-P')
  let D := localLog d - (R'-P')
  have fs {u v : HeightPlace K → ℝ} (h₁ : FiniteAtPrimes u) (h₂ : FiniteAtPrimes v) :
      FiniteAtPrimes (u-v) := by rw [sub_eq_add_neg]; exact finite_add h₁ (finite_neg h₂)
  have h₁ : FiniteAtPrimes A := fs (finiteLog ha) (fs hR hP)
  have h₂ : FiniteAtPrimes B := fs (finiteLog hb) (fs hR' hP)
  have h₃ : FiniteAtPrimes C := fs (finiteLog hc) (fs hR hP')
  have h₄ : FiniteAtPrimes D := fs (finiteLog hd) (fs hR' hP')
  have h := twice_weilHeight_eq_absLog (div_ne_zero (mul_ne_zero ha hd) (mul_ne_zero hb hc))
  change 2 * weilHeight (a*d/(b*c)) = placeNorm (localLog (a*d/(b*c))) at h
  have cancel : localLog (a*d/(b*c)) = ((A+D)+(-B))+(-C) := by
    rw [localLog_rectangle ha hb hc hd]
    dsimp only [A,B,C,D]
    abel
  rw [cancel] at h
  have first := placeNorm_add A D h₁ h₄
  have second := placeNorm_add (A+D) (-B) (finite_add h₁ h₄) (finite_neg h₂)
  have third := placeNorm_add ((A+D)+(-B)) (-C) (finite_add (finite_add h₁ h₄) (finite_neg h₂))
    (finite_neg h₃)
  simp only [placeNorm_neg] at second third
  change placeNorm A ≤ s at ea
  change placeNorm B ≤ s at eb
  change placeNorm C ≤ s at ec
  change placeNorm D ≤ s at ed
  linarith

end PlanarUnitDistances

