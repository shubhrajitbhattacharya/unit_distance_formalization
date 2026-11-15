import PlanarUnitDistances.PlaceAverage
import PlanarUnitDistances.WalkError

namespace PlanarUnitDistances.Competition.IncidencePiece
open Finset NumberField Real
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

def commonDisagreement (M : IncidencePiece K) (r : CoordinateLevel M.Label) := M.walkLinear (M.commonBitError r)

private theorem bad_le (M : IncidencePiece K) (r : CoordinateLevel M.Label) :
    M.badWidth r≤(1/eps)*M.inconsistentMass r := by
  have ep : 0<eps := by unfold eps; positivity
  by_cases h : M.minorityMass r<eps ∧ eps<M.inconsistentMass r
  · rw [badWidth,ite_eq_left h,one_div,←div_eq_inv_mul,le_div_iff₀ ep,one_mul]; exact h.2.le
  · rw [badWidth,ite_eq_right h]
    exact mul_nonneg (div_nonneg zero_le_one ep.le) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

private theorem record_mean_le (M : IncidencePiece K) (hn : M.E.Nonempty) (d : CoordinateLevel M.Label → M.Label)
    (r : CoordinateLevel M.Label) :
    M.walkLinear (fun v => M.recordError d v r)≤
      4*M.masked (fun j => M.edgeException j (d j)) r+(4+1/eps)*M.inconsistentMass r+
      2*M.masked (fun j => M.walkException j (d j)) r+M.commonDisagreement r := by
  let err (v : Triple M) := M.masked (fun j => rareTripleError j (d j) v) r
  change M.walkLinear (err+M.commonBitError r+(fun _ => M.badWidth r))≤_
  rw [map_add,map_add,walkLinear_const M hn]
  change M.walkLinear err+M.commonDisagreement r+M.badWidth r≤_
  have bad := bad_le M r
  have mnn : 0≤M.inconsistentMass r := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  by_cases hg : M.goodRare r
  · have eq : err=rareTripleError r (d r) := funext (fun _ => ite_eq_left hg)
    rw [eq,average_rare_error]; simp only [masked,hg,ite_true]; linarith only [bad]
  · have eq : err=(fun _ => 0) := funext (fun _ => ite_eq_right hg)
    rw [eq,walkLinear_const M hn]; simp only [masked,hg,ite_false]; linarith only [bad,mnn]

private theorem interchange (M : IncidencePiece K) (F : Finset (FinitePlace K)) (l h : AbsoluteValue K ℝ → ℝ)
    (u : InfinitePlace K → ℝ) (g : Triple M→CoordinateLevel M.Label→ℝ) :
    M.walkLinear (fun v => M.placeIntegral F l h u (g v))=
    M.placeIntegral F l h u (fun r => M.walkLinear fun v => g v r) := by
  let T := M.placeLinear F l h u
  have hT (f : CoordinateLevel M.Label→ℝ) : M.placeIntegral F l h u f=T f := (placeLinear_apply M F l h u f).symm
  simp_rw [hT]
  change (∑v,M.mass v*T (g v))=T (fun r => ∑v,M.mass v*g v r)
  have eq : (fun r => ∑v,M.mass v*g v r)=∑v,M.mass v • g v := by
    funext r; simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [eq,map_sum]; simp only [map_smul,smul_eq_mul]

/-- The expectation of the explicit error on physical triples, for
arbitrary physical shifts and labels, with every term on the same law. -/
theorem physical_error_budget (M : IncidencePiece K) (hn : M.E.Nonempty) (F : Finset (FinitePlace K))
    (l h : AbsoluteValue K ℝ → ℝ) (u : InfinitePlace K → ℝ) (d : CoordinateLevel M.Label → M.Label) :
    M.walkLinear (fun v => M.placeIntegral F l h u (M.recordError d v))≤
      4*M.placeIntegral F l h u (M.masked fun j => M.edgeException j (d j))+
      (4+1/eps)*M.placeIntegral F l h u M.inconsistentMass+
      2*M.placeIntegral F l h u (M.masked fun j => M.walkException j (d j))+
      M.placeIntegral F l h u M.commonDisagreement := by
  rw [interchange]
  apply (placeIntegral_mono M F l h u (record_mean_le M hn d)).trans_eq
  let T := M.placeLinear F l h u
  let J := M.masked (fun j => M.edgeException j (d j))
  let W := M.masked (fun j => M.walkException j (d j))
  have hT (f : CoordinateLevel M.Label→ℝ) : M.placeIntegral F l h u f=T f := (placeLinear_apply M F l h u f).symm
  simp_rw [hT]
  change T ((4:ℝ) • J+(4+1/eps) • M.inconsistentMass+(2:ℝ) • W+M.commonDisagreement)=
    4*T J+(4+1/eps)*T M.inconsistentMass+2*T W+T M.commonDisagreement
  simp only [map_add,map_smul,smul_eq_mul]

/-- The chosen common shifts and dominant labels, with the only remaining
mean-error input being the common-level bit disagreement on these very
shifts. The error Z of each triple is defined by place integration, with
no independent copy of the edge or walk. -/
theorem physical_error_mean (M : IncidencePiece K) {t : ℝ} (reg : Regular M t) (ht : 0<t)
    (hx : t^(-150*savingG)≤(2:ℝ)^(-154:ℝ)) (hS : (2:ℝ)^2100≤M.scale)
    (F : Finset (FinitePlace K)) (active : ∀v∉F,∀e∈M.E,M.threshold v e=0)
    (l h : AbsoluteValue K ℝ → ℝ)
    (lo : ∀(v : AbsoluteValue K ℝ) e,e∈M.E → l v≤M.threshold v e)
    (hi : ∀(v : AbsoluteValue K ℝ) e,e∈M.E → M.threshold v e≤h v) :
    ∃ (u : InfinitePlace K → ℝ) (d : CoordinateLevel M.Label → M.Label),
      (∀v,u v∈Set.Ioo (0:ℝ) 1) ∧ (∀r,M.goodRare r →
        M.pointMass (fun p => r.selected p≠d r)+M.centerMass (fun q => r.selected q≠d r)
        ≤2*(M.minorityMass r+M.inconsistentMass r)) ∧
      M.placeIntegral F l h u M.minorityMass=M.scale ∧
      M.placeIntegral F l h u M.inconsistentMass≤2*sqrt 2 ∧
      M.placeIntegral F l h u (M.masked fun r => M.edgeException r (d r))≤5*(2:ℝ)^(-144:ℝ)*M.scale ∧
      M.placeIntegral F l h u (M.masked fun r => M.walkException r (d r))≤(2:ℝ)^(-144:ℝ)*M.scale ∧
      (M.placeIntegral F l h u M.commonDisagreement≤2048*(2:ℝ)^(-144:ℝ)*M.scale →
        M.walkLinear (fun v => M.placeIntegral F l h u (M.recordError d v))≤
        2071*(2:ℝ)^(-144:ℝ)*M.scale ∧
        M.walkLinear (fun v => M.placeIntegral F l h u (M.recordError d v))<
        2^12*(2:ℝ)^(-144:ℝ)*M.scale) := by
  have four (n : ℕ) (hn : 2≤n) : (4:ℝ)≤2^n := by
    rw [show (4:ℝ)=(2:ℝ)^2 by norm_num]
    exact pow_le_pow_right₀ (by norm_num) hn
  have s4 : 4≤M.scale := (four 2100 (by decide)).trans hS
  obtain ⟨u,d,hu,hd,correct,err,je,jw⟩ := physical_rare M reg ht hx s4 F active l h lo hi
  refine ⟨u,d,hu,hd,correct,err,je,jw,?_⟩
  intro common
  have he : 0<(M.E.card:ℝ) := (rpow_pos_of_pos ht _).trans_le reg.size
  have budget := physical_error_budget M (card_pos.mp (Nat.cast_pos.mp he)) F l h u d
  have ep : 0<eps := by unfold eps; positivity
  have ern : M.placeIntegral F l h u M.inconsistentMass≤4 := by
    nlinarith only [err,sq_sqrt (by norm_num : (0:ℝ)≤2),sq_nonneg (sqrt 2-2)]
  have eb : (4+1/eps)*M.placeIntegral F l h u M.inconsistentMass≤(2:ℝ)^(-144:ℝ)*M.scale := by
    apply (mul_le_mul_of_nonneg_left ern (by positivity)).trans
    apply le_trans _ (mul_le_mul_of_nonneg_left hS (by positivity))
    have invε : 1/eps=(2:ℝ)^1800 := by norm_num [eps]
    have pw : (2:ℝ)^(-144:ℝ)*(2:ℝ)^2100=(2:ℝ)^1956 := by
      rw [←rpow_natCast _ 2100,←rpow_natCast _ 1956,←rpow_add (by norm_num)]
      congr 1; norm_num
    rw [invε,pw]
    calc
      _ ≤ ((2:ℝ)^1800+2^1800)*4 := mul_le_mul_of_nonneg_right (add_le_add (four 1800 (by decide)) le_rfl) (by norm_num)
      _ = (2:ℝ)^1803 := by
        rw [show 1803=1800+3 by decide,pow_add]
        generalize (2:ℝ)^1800=z
        ring
      _ ≤ (2:ℝ)^1956 := pow_le_pow_right₀ (by norm_num) (by decide : (1803:ℕ)≤1956)
  have nn : 0<(2:ℝ)^(-144:ℝ)*M.scale := mul_pos (rpow_pos_of_pos (by norm_num) _) (lt_of_lt_of_le (by norm_num) s4)
  have total := budget.trans (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left je (by norm_num : (0:ℝ)≤4))
    eb) (mul_le_mul_of_nonneg_left jw (by norm_num : (0:ℝ)≤2))) common)
  have bound : M.walkLinear (fun v => M.placeIntegral F l h u (M.recordError d v))≤2071*(2:ℝ)^(-144:ℝ)*M.scale :=
    total.trans_eq (by ring)
  refine ⟨bound,bound.trans_lt ?_⟩
  simpa only [mul_assoc] using mul_lt_mul_of_pos_right (by norm_num : (2071:ℝ)<2^12) nn

end
end PlanarUnitDistances.Competition.IncidencePiece
