import PlanarUnitDistances.AllPlaceRare

namespace PlanarUnitDistances.Competition.IncidencePiece
open Finset MeasureTheory NumberField Set
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

def recordIntegral {B : Type*} (R : SimpleFunc ℝ B) (l h : ℝ) : (B→ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫s in Icc l h,f (R s)
  map_add' f g := integral_add (R.map f).integrable_of_isFiniteMeasure (R.map g).integrable_of_isFiniteMeasure
  map_smul' _ _ := integral_const_mul ..

def placeLinear (M : IncidencePiece K) (F : Finset (FinitePlace K))
    (l h : AbsoluteValue K ℝ → ℝ) (u : InfinitePlace K → ℝ) : (CoordinateLevel M.Label→ℝ) →ₗ[ℝ] ℝ :=
  (Module.finrank ℚ K:ℝ)⁻¹ • ((∑v : InfinitePlace K,(v.mult:ℝ) •
    recordIntegral (archRecord M v (u v,u v) (u v,u v)) (l v.val) (h v.val))+
    ∑v∈F,recordIntegral (finiteRecord M v) (l v.val) (h v.val))

theorem placeLinear_apply (M : IncidencePiece K) (F : Finset (FinitePlace K))
    (l h : AbsoluteValue K ℝ → ℝ) (u : InfinitePlace K → ℝ) (f : CoordinateLevel M.Label → ℝ) :
    M.placeLinear F l h u f=M.placeIntegral F l h u f := by
  simp [placeLinear,placeIntegral,recordIntegral,LinearMap.sum_apply,div_eq_inv_mul,mul_add]

theorem placeIntegral_mono (M : IncidencePiece K) (F : Finset (FinitePlace K)) (l h : AbsoluteValue K ℝ → ℝ)
    (u : InfinitePlace K → ℝ) {f g : CoordinateLevel M.Label → ℝ} (hfg : ∀r,f r≤g r) :
    M.placeIntegral F l h u f ≤ M.placeIntegral F l h u g := by
  have mono (R : SimpleFunc ℝ (CoordinateLevel M.Label)) (l h : ℝ) :
      (∫s in Icc l h,f (R s))≤∫s in Icc l h,g (R s) :=
    integral_mono (R.map f).integrable_of_isFiniteMeasure (R.map g).integrable_of_isFiniteMeasure (fun s => hfg _)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact add_le_add (sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (mono _ _ _) (Nat.cast_nonneg _)))
    (sum_le_sum (fun v _ => mono _ _ _))

end
end PlanarUnitDistances.Competition.IncidencePiece
