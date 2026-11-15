import PlanarUnitDistances.ErrorRecord
import PlanarUnitDistances.PlaceAverage
import PlanarUnitDistances.ThresholdInterval

namespace PlanarUnitDistances.Competition.IncidencePiece
open Real Finset MeasureTheory Set
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

def endpointWidth (M : IncidencePiece K) (d : CoordinateLevel M.Label→M.Label) (p : Plane) :=
  M.masked fun r => r.exceptionAt (d r) p

def endpointSigned (M : IncidencePiece K) (d : CoordinateLevel M.Label→M.Label) (p : Plane) :=
  M.masked fun r => r.bitSign*r.exceptionAt (d r) p

def bitDifference (M : IncidencePiece K) (v : Triple M) (r : CoordinateLevel M.Label) :=
  bitValue (r.bit (v.1.val,v.2.1.val))-bitValue (r.bit (v.2.2.val,v.2.1.val))

theorem recordError_comparison (M : IncidencePiece K) (d : CoordinateLevel M.Label → M.Label)
    (v : Triple M) (r : CoordinateLevel M.Label) :
    let p := v.1.val
    let x := v.2.2.val
    let w := M.endpointWidth d p r+M.endpointWidth d x r
    let b := M.bitDifference v r
    let err := M.recordError d v r
    |b-(M.endpointSigned d p r-M.endpointSigned d x r)|≤err ∧
    w-err≤|b| ∧ |b|≤w+err := by
  dsimp only
  let p := v.1.val
  let q := v.2.1.val
  let x := v.2.2.val
  let a := d r
  let u := r.twoEdgeError a p q x
  let ip := r.exceptionAt a p
  let ix := r.exceptionAt a x
  let b := M.bitDifference v r
  have ip0 : 0 ≤ ip := by dsimp [ip,CoordinateLevel.exceptionAt]; split <;> norm_num
  have ix0 : 0 ≤ ix := by dsimp [ix,CoordinateLevel.exceptionAt]; split <;> norm_num
  have corr : 0≤2*ip*ix := mul_nonneg (mul_nonneg (by norm_num) ip0) ix0
  have sg : |r.bitSign|=1 := by cases hm : r.majority <;> norm_num [CoordinateLevel.bitSign,bitValue,hm]
  have sc : |r.bitSign*(ip-ix)| ≤ ip+ix := by
    rw [abs_mul,sg,one_mul]; exact abs_le.mpr ⟨by linarith,by linarith⟩
  have sign := subtract_edges r a p q x
  change |b-r.bitSign*(ip-ix)|≤u at sign
  have unsign := subtract_edges_unsigned r a p q x
  change ip+ix-2*ip*ix-u≤|b| at unsign
  have large : |b| ≤ ip+ix+u := by
    calc
      _ = |(b-r.bitSign*(ip-ix))+r.bitSign*(ip-ix)| := by rw [sub_add_cancel]
      _ ≤ _ := (abs_add_le ..).trans ((add_le_add sign sc).trans_eq (add_comm ..))
  have sm : |b|≤1 := by
    dsimp [b,bitDifference,bitValue]; split <;> split <;> norm_num
  by_cases hg : M.goodRare r
  · have hc := not_le_of_gt hg.1
    have hm := not_lt_of_ge hg.2
    simp only [recordError,endpointWidth,endpointSigned,masked,hg,ite_true,commonBitError,hc,ite_false,
      badWidth,hm,and_false,rareTripleError,add_zero]
    change |b-(r.bitSign*ip-r.bitSign*ix)|≤u+2*ip*ix ∧
      ip+ix-(u+2*ip*ix)≤|b| ∧ |b| ≤ ip+ix+(u+2*ip*ix)
    rw [←mul_sub]
    exact ⟨sign.trans (le_add_of_nonneg_right corr),by linarith only [unsign],by linarith only [large,corr]⟩
  · by_cases hc : eps≤M.minorityMass r
    · have hf := not_lt_of_ge hc
      simp [recordError,endpointWidth,endpointSigned,masked,hg,commonBitError,hc,badWidth,hf,bitDifference]
    · have f := lt_of_not_ge hc
      have m : eps<M.inconsistentMass r := lt_of_not_ge (fun hm => hg ⟨f,hm⟩)
      simp only [recordError,endpointWidth,endpointSigned,masked,hg,ite_false,commonBitError,hc,
        badWidth,f,m,and_self,ite_true,zero_add,sub_zero,add_zero]
      exact ⟨sm,by linarith only [abs_nonneg b],sm⟩

/-- Signed and two-sided unsigned comparisons on a whole interval for
an actual record map with the two prescribed original threshold bits. -/
theorem local_endpoint (M : IncidencePiece K) (d : CoordinateLevel M.Label→M.Label)
    (v : Triple M) (R : SimpleFunc ℝ (CoordinateLevel M.Label)) (l h n n' : ℝ)
    (ln : l≤n) (ln' : l≤n') (nh : n≤h) (nh' : n'≤h)
    (bits : ∀s,M.bitDifference v (R s)=thresholdBit n s-thresholdBit n' s) :
    let T := recordIntegral R l h
    let w := T (M.endpointWidth d v.1.val)+T (M.endpointWidth d v.2.2.val)
    let a := T (M.endpointSigned d v.1.val)-T (M.endpointSigned d v.2.2.val)
    let z := T (M.recordError d v)
    |(n-n')-a|≤z ∧ w-z≤|n-n'| ∧ |n-n'|≤w+z := by
  let T := recordIntegral R l h
  let A := M.endpointSigned d v.1.val-M.endpointSigned d v.2.2.val
  let W := M.endpointWidth d v.1.val+M.endpointWidth d v.2.2.val
  let B := M.bitDifference v
  let N (r : CoordinateLevel M.Label) := |B r|
  let E := M.recordError d v
  have mono {f g : CoordinateLevel M.Label→ℝ} (hfg : ∀r,f r≤g r) : T f≤T g :=
    integral_mono (R.map f).integrable_of_isFiniteMeasure (R.map g).integrable_of_isFiniteMeasure (fun s => hfg _)
  have point (r : CoordinateLevel M.Label) := recordError_comparison M d v r
  have sl : T (-E)≤T (B-A) := mono (fun r => (abs_le.mp (point r).1).1)
  have sr : T (B-A)≤T E := mono (fun r => (abs_le.mp (point r).1).2)
  have ul : T (W-E)≤T N := mono (fun r => (point r).2.1)
  have ur : T N≤T (W+E) := mono (fun r => (point r).2.2)
  have th := threshold_difference ln ln' nh nh'
  have tb : T B=n-n' := by
    change (∫s in Icc l h,M.bitDifference v (R s))=n-n'
    simp_rw [bits]; exact th.1
  have tn : T N=|n-n'| := by
    change (∫s in Icc l h,|M.bitDifference v (R s)|)=|n-n'|
    simp_rw [bits]; exact th.2
  simp only [map_neg,map_sub,tn,tb,map_add,A,W] at sl sr ul ur
  exact ⟨abs_le.mpr ⟨sl,sr⟩,ul,ur⟩

end
end PlanarUnitDistances.Competition.IncidencePiece
