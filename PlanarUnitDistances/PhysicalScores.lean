import PlanarUnitDistances.LocalEndpoint
import PlanarUnitDistances.ArithmeticBits

namespace PlanarUnitDistances.Competition.IncidencePiece
open Real Finset NumberField MeasureTheory
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

abbrev Place (K : Type) [Field K] [NumberField K] := InfinitePlace K ⊕ FinitePlace K
def valuation : Place K → AbsoluteValue K ℝ :=
  Sum.elim (fun v : InfinitePlace K => v.val) (fun v : FinitePlace K => v.val)

def placeSum (F : Finset (FinitePlace K)) (f : Place K→ℝ) :=
  ((∑v : InfinitePlace K,(v.mult:ℝ)*f (.inl v))+(∑v∈F,f (.inr v)))/(Module.finrank ℚ K:ℝ)

private theorem sum_mono (F : Finset (FinitePlace K)) {f g : Place K → ℝ}
    (ha : ∀v : InfinitePlace K,f (.inl v)≤g (.inl v))
    (hf : ∀v∈F,f (.inr v)≤g (.inr v)) : placeSum F f≤placeSum F g := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact add_le_add (sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (ha v) (Nat.cast_nonneg _))) (sum_le_sum hf)

private theorem sum_add (F : Finset (FinitePlace K)) (f g : Place K → ℝ) :
    placeSum F (f+g)=placeSum F f+placeSum F g := by
  simp only [placeSum,Pi.add_apply,mul_add,sum_add_distrib]; ring

private theorem sum_sub (F : Finset (FinitePlace K)) (f g : Place K → ℝ) :
    placeSum F (f-g)=placeSum F f-placeSum F g := by
  simp only [placeSum,Pi.sub_apply,mul_sub,sum_sub_distrib]; ring

def recordsAt (M : IncidencePiece K) (u : InfinitePlace K→ℝ) : Place K→SimpleFunc ℝ (CoordinateLevel M.Label) :=
  Sum.elim (fun v => archRecord M v (u v,u v) (u v,u v)) (fun v => finiteRecord M v)

def valueAt (M : IncidencePiece K) (l h : AbsoluteValue K ℝ→ℝ) (u : InfinitePlace K→ℝ)
    (f : CoordinateLevel M.Label→ℝ) (v : Place K) :=
  recordIntegral (M.recordsAt u v) (l (valuation v)) (h (valuation v)) f

/-- The scores are fixed functions of the endpoints, and the actual
triple error is integrated from the same level records. -/
def arithmeticScores (M : IncidencePiece K) (F : Finset (FinitePlace K)) (l h : AbsoluteValue K ℝ→ℝ)
    (u : InfinitePlace K→ℝ) (d : CoordinateLevel M.Label→M.Label) : Scores M where
  H p := M.placeIntegral F l h u (M.endpointWidth d p.val)
  arch p v := M.valueAt l h u (M.endpointSigned d p.val) (.inl v)
  finite p := Finsupp.onFinset F (fun v => if v∈F then M.valueAt l h u (M.endpointSigned d p.val) (.inr v) else 0)
    (by intro v hv; by_contra hn; exact hv (ite_eq_right hn))
  error x := M.placeIntegral F l h u (M.recordError d x)

theorem arithmeticScores_nonneg (M : IncidencePiece K) (F : Finset (FinitePlace K))
    (l h : AbsoluteValue K ℝ→ℝ) (u : InfinitePlace K→ℝ) (d : CoordinateLevel M.Label→M.Label) :
    let S := M.arithmeticScores F l h u d
    (∀p,0≤S.H p) ∧ (∀x,0≤S.error x) := by
  have nn (f : CoordinateLevel M.Label→ℝ) (hf : ∀r,0≤f r) : 0≤M.placeIntegral F l h u f := by
    have zero : M.placeIntegral F l h u (0 : CoordinateLevel M.Label→ℝ)=0 :=
      (placeLinear_apply M F l h u 0).symm.trans (map_zero _)
    rw [←zero]; exact placeIntegral_mono M F l h u hf
  constructor
  · intro p; apply nn
    intro r
    by_cases j : M.goodRare r <;> by_cases eq : r.selected p.val=d r <;>
      simp [endpointWidth,masked,CoordinateLevel.exceptionAt,j,eq]
  · intro x; exact nn _ fun r => (abs_nonneg _).trans (recordError_comparison M d x r).1

private theorem bits_at (M : IncidencePiece K) (u : InfinitePlace K→ℝ) (x : Triple M) (hx : 0<M.mass x)
    (v : Place K) (s : ℝ) : M.bitDifference x (M.recordsAt u v s)=
    thresholdBit (M.threshold (valuation v) (x.1.val,x.2.1.val)) s-
    thresholdBit (M.threshold (valuation v) (x.2.2.val,x.2.1.val)) s := by
  obtain ⟨p,r⟩ := supported_edges M x hx
  have test (c k : Prop) (i : Decidable c) (j : Decidable k) (ck : c↔k) :
      bitValue (@decide c i)=@ite ℝ k j 1 0 := by
    by_cases hc : c
    · rw [@decide_eq_true c i hc,if_pos (ck.mp hc)]; rfl
    · rw [@decide_eq_false c i hc,if_neg (fun hk => hc (ck.mpr hk))]; rfl
  cases v with
  | inl v => simp only [recordsAt,Sum.elim_inl,bitDifference,arch_bit M v _ _ _ _ p,
      arch_bit M v _ _ _ _ r,thresholdBit,valuation,threshold,InfinitePlace.coe_apply]
             apply congrArg₂ (fun a b : ℝ => a-b) <;> apply test <;> rfl
  | inr v => simp only [recordsAt,Sum.elim_inr,bitDifference,finite_edge_bit M v _ _ p,
      finite_edge_bit M v _ _ r,thresholdBit,valuation,threshold,FinitePlace.coe_apply]
             apply congrArg₂ (fun a b : ℝ => a-b) <;> apply test <;> rfl

/-- Both endpoint comparisons of the manuscript on every supported
triple, including repeated points, with a single explicit family of
arithmetic endpoint scores and one integrated error. -/
theorem physical_endpoints (M : IncidencePiece K) (F : Finset (FinitePlace K))
    (active : ∀v∉F,∀e∈M.E,M.threshold v e=0) (l h : AbsoluteValue K ℝ → ℝ)
    (lo : ∀(v : AbsoluteValue K ℝ) e,e∈M.E → l v≤M.threshold v e)
    (hi : ∀(v : AbsoluteValue K ℝ) e,e∈M.E → M.threshold v e≤h v)
    (u : InfinitePlace K → ℝ) (d : CoordinateLevel M.Label → M.Label) (x : Triple M) (hx : 0<M.mass x) :
    let S := M.arithmeticScores F l h u d
    signedError S x≤S.error x ∧ |2*weilHeight (tripleRatio M x)-S.width x|≤S.error x := by
  let S := M.arithmeticScores F l h u d
  let E := M.valueAt l h u (M.recordError d x)
  let W := M.valueAt l h u (M.endpointWidth d x.1.val)+M.valueAt l h u (M.endpointWidth d x.2.2.val)
  let A := M.valueAt l h u (M.endpointSigned d x.2.2.val)-M.valueAt l h u (M.endpointSigned d x.1.val)
  let B (v : Place K) := Real.log (valuation v (tripleRatio M x))
  let N (v : Place K) := |B v|
  let D (v : Place K) := |B v-A v|
  obtain ⟨hp,hr⟩ := supported_edges M x hx
  have point (v : Place K) : D v≤E v ∧ W v-E v≤N v ∧ N v≤W v+E v := by
    let v' := valuation v
    have z := local_endpoint M d x (M.recordsAt u v) (l v') (h v') _ _ (lo v' _ hp) (lo v' _ hr)
      (hi v' _ hp) (hi v' _ hr) (bits_at M u x hx v)
    dsimp only at z
    have rev := threshold_ratio M x hx v'
    change B v=_ at rev
    have sn := abs_le.mp z.1
    change |B v-(_-_)|≤_ ∧ _≤|B v| ∧ |B v|≤_
    rw [rev,abs_sub_comm (M.threshold v' (x.2.2.val,x.2.1.val)) (M.threshold v' (x.1.val,x.2.1.val))]
    refine ⟨abs_le.mpr ⟨?_,?_⟩,z.2.1,z.2.2⟩ <;> dsimp only [valueAt,E] <;> linarith only [sn.1,sn.2]
  have zero (v : FinitePlace K) (hv : v∉F) : B (.inr v)=0 := by
    have eq (e : Plane×Plane) : M.threshold v.val e=M.threshold v e := by simp only [threshold,FinitePlace.coe_apply]
    exact (threshold_ratio M x hx v.val).trans (by
      rw [eq (x.2.2.val,x.2.1.val),eq (x.1.val,x.2.1.val),active v hv _ hr,active v hv _ hp,sub_self])
  have width : S.width x=placeSum F W :=
    (sum_add F (M.valueAt l h u (M.endpointWidth d x.1.val)) (M.valueAt l h u (M.endpointWidth d x.2.2.val))).symm
  have error : S.error x=placeSum F E := rfl
  have norm : 2*weilHeight (tripleRatio M x)=placeSum F N := by
    rw [twice_weilHeight_eq_absLog (ratio_ne M x hx)]
    unfold placeSum
    congr 2
    apply finsum_eq_sum_of_support_subset
    intro v hv; by_contra hn
    exact hv ((congrArg abs (zero v hn)).trans abs_zero)
  have finiteScore (p : M.P) (v : FinitePlace K) : S.finite p v=
      if v∈F then M.valueAt l h u (M.endpointSigned d p.val) (.inr v) else 0 := rfl
  have signed : signedError S x=placeSum F D := by
    unfold signedError placeSum
    congr 2
    have eq : (∑ᶠv : FinitePlace K, |Real.log (v (tripleRatio M x))-(S.finite x.2.2 v-S.finite x.1 v)|)=
      ∑v∈F,|Real.log (v (tripleRatio M x))-(S.finite x.2.2 v-S.finite x.1 v)| := by
      apply finsum_eq_sum_of_support_subset
      intro v hv; by_contra hn
      have hn' : v∉F := hn
      change |B (.inr v)-(S.finite x.2.2 v-S.finite x.1 v)|≠0 at hv
      simp [finiteScore,hn',zero v hn'] at hv
    rw [eq]; apply sum_congr rfl; intro v hv; simp [D,A,B,valuation,finiteScore,hv,FinitePlace.coe_apply]
  change signedError S x≤S.error x ∧ |2*weilHeight (tripleRatio M x)-S.width x|≤S.error x
  rw [signed,width,error,norm]
  have low := sum_mono F (f:=W-E) (g:=N) (fun v => (point (.inl v)).2.1) (fun v _ => (point (.inr v)).2.1)
  have high := sum_mono F (f:=N) (g:=W+E) (fun v => (point (.inl v)).2.2) (fun v _ => (point (.inr v)).2.2)
  rw [sum_sub] at low; rw [sum_add] at high
  exact ⟨sum_mono F (fun v => (point (.inl v)).1) (fun v _ => (point (.inr v)).1),
    abs_le.mpr ⟨by linarith only [low],by linarith only [high]⟩⟩

end
end PlanarUnitDistances.Competition.IncidencePiece
