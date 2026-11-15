import PlanarUnitDistances.FixedPairRecord
import PlanarUnitDistances.ArithmeticTailMeans

namespace PlanarUnitDistances.Competition.IncidencePiece
open Real Finset NumberField
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

/-- Converting the fixed-pair product-formula estimate in manuscript (budnew-rarealone)
to the distinct-neighbor width inequality used by the edge-truncation argument. -/
theorem width_pair_of_rare_score (M : IncidencePiece K) (F : Finset (FinitePlace K))
    (l h : AbsoluteValue K ℝ→ℝ) (u : InfinitePlace K→ℝ) (d : CoordinateLevel M.Label→M.Label)
    (hS : (2:ℝ)^2100 < M.scale) (hmin : M.placeIntegral F l h u M.minorityMass=M.scale)
    (hbad : M.placeIntegral F l h u M.inconsistentMass≤2*sqrt 2)
    (p q q' : Plane) (hscore : M.placeIntegral F l h u (M.rarePairScore d p q q')≤2*log 2) :
    2*M.vertexWidth F l h u d p ≤ 3*(M.vertexWidth F l h u d q+M.inconsistentLength F l h u (p,q)+
      (M.vertexWidth F l h u d q'+M.inconsistentLength F l h u (p,q')))+2*M.scale/eps := by
  let L := M.placeLinear F l h u
  have Lmono {v w : CoordinateLevel M.Label→ℝ} (z : ∀r,v r≤w r) : L v ≤ L w := by
    dsimp [L]
    rw [placeLinear_apply,placeLinear_apply]
    exact M.placeIntegral_mono F l h u z
  let outside (r : CoordinateLevel M.Label) : ℝ := if M.goodRare r then 0 else 1
  let err (e : Plane×Plane) (r : CoordinateLevel M.Label) := r.errorAt e
  have err_eq (e : Plane×Plane) : L (err e) = M.inconsistentLength F l h u e := by
    rw [show L (err e)=M.placeIntegral F l h u (err e) from M.placeLinear_apply F l h u _]
    apply congrArg (M.placeIntegral F l h u)
    funext r
    by_cases c : r.consistent e <;> simp [err,CoordinateLevel.errorAt,c]
  let W := M.endpointWidth d
  have wx (x : Plane) : L (W x)=M.vertexWidth F l h u d x := M.placeLinear_apply F l h u _
  have pt : L ((2:ℝ) • W p) ≤ L ((3:ℝ) • (W q+W q'+err (p,q)+err (p,q'))+
        M.rarePairScore d p q q'+outside) :=
    Lmono (M.rare_pair_lower_record d p q q')
  simp only [map_smul,map_add,smul_eq_mul,wx,err_eq] at pt
  have ep : 0<eps := by unfold eps; positivity
  have ep1 : eps≤1 := by unfold eps; apply Real.rpow_le_one_of_one_le_of_nonpos <;> norm_num
  have Lmin : L M.minorityMass=M.scale := (M.placeLinear_apply F l h u _).trans hmin
  have Lbad : L M.inconsistentMass≤4 := (M.placeLinear_apply F l h u _).trans_le (hbad.trans
    (by nlinarith [sq_sqrt (by norm_num : (0:ℝ)≤2),sq_nonneg (sqrt 2-2)]))
  have mass : L (eps • outside) ≤ L (M.minorityMass+M.inconsistentMass) := by
    apply Lmono
    intro r
    have f : 0≤M.minorityMass r := by unfold minorityMass edgeProb; positivity
    have m : 0≤M.inconsistentMass r := by unfold inconsistentMass edgeProb; positivity
    change eps*outside r ≤ M.minorityMass r+M.inconsistentMass r
    by_cases hr : M.goodRare r
    · simp [outside,hr,add_nonneg f m]
    · simp only [outside,ite_eq_right hr,mul_one]
      change ¬(M.minorityMass r<eps ∧ M.inconsistentMass r≤eps) at hr
      rcases not_and_or.mp hr with a | a
      · linarith [le_of_not_gt a]
      · linarith [lt_of_not_ge a]
  simp only [map_smul,smul_eq_mul,map_add,Lmin] at mass
  have sc : L (M.rarePairScore d p q q')≤2*log 2 := (M.placeLinear_apply F l h u _).trans_le hscore
  have S8 : 8≤M.scale := (show (8:ℝ)=2^3 by norm_num).trans_le
    ((pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by decide : (3:ℕ)≤2100)).trans hS.le)
  have log2 : log 2≤1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have budget : L (M.rarePairScore d p q q')+L outside≤2*M.scale/eps := by
    apply (le_div_iff₀ ep).mpr
    have loge := mul_le_mul_of_nonneg_right (sc.trans (mul_le_mul_of_nonneg_left log2 (by norm_num : (0:ℝ)≤2))) ep.le
    rw [add_mul]
    linarith only [mass,Lbad,loge,ep1,S8]
  linarith only [pt,budget]

end
end PlanarUnitDistances.Competition.IncidencePiece


