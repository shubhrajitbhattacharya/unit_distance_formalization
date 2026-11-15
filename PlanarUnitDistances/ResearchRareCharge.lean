import PlanarUnitDistances.ResearchRareFlanks

namespace PlanarUnitDistances.ResearchPhysical
open Competition Competition.IncidencePiece Real NumberField Finset Set MeasureTheory
open OAI.PlanarUnitDistances.BudgetPlaces
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

private theorem eps_half : eps≤1/2 := by
  calc
    eps ≤ (2:ℝ)^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = _ := by norm_num

private theorem rare_positive_integral (M : IncidencePiece K) (u : InfinitePlace K→ℝ) (v : Place K)
    (d : CoordinateLevel M.Label→M.Label) {p q r : Competition.Plane}
    (he : (p,q)∈M.E) (he' : (p,r)∈M.E) (hne : q≠r)
    (hord : M.threshold (valuation v) (p,q)≤M.threshold (valuation v) (p,r)) (l h : ℝ) :
    recordIntegral (M.recordsAt u v) l h (M.rarePairPositive d p q r)
        ≤2*(alpha (valuation v) (jump M p q) (jump M p r)+flankConstant v) := by
  let T := alpha (valuation v) (jump M p q) (jump M p r)+flankConstant v
  let R := M.recordsAt u v
  let A := M.rarePairPositive d p q r
  let b := M.threshold (valuation v) (p,q)
  let b' := M.threshold (valuation v) (p,r)
  have hT : 0≤T := flank_length_nonneg M he he' hne v
  have flank (s : ℝ) (n : A (R s)≠0) := rare_flanks M u v d he he' hne hord s n
  have single : ∃x y : ℝ, y-x=T ∧ ∀s,A (R s)≠0 → s∈Icc x y := by
    by_cases left : ∃s,A (R s)≠0 ∧ (R s).majority=false
    · obtain ⟨s0,n0,m0⟩ := left
      obtain ⟨mem0,f0⟩ := (flank s0 n0).1 m0
      refine ⟨b-T,b,by ring,?_⟩
      intro s n
      cases hm : (R s).majority with
      | false => exact ((flank s n).1 hm).1
      | true =>
        obtain ⟨mem',f'⟩ := (flank s n).2 hm
        have ht := frequency_antitone M v (mem0.2.trans (hord.trans mem'.1))
        linarith only [f0,f',ht,eps_half]
    · refine ⟨b',b'+T,by ring,?_⟩
      intro s n
      cases hm : (R s).majority with
      | false => exact (left ⟨s,n,hm⟩).elim
      | true => exact ((flank s n).2 hm).1
  obtain ⟨x,y,hxy,hs⟩ := single
  have iB : Integrable ((Icc x y).indicator (fun _ : ℝ => (2:ℝ))) volume :=
    ((continuous_const : Continuous (fun _ : ℝ => (2:ℝ))).integrableOn_Icc).integrable_indicator measurableSet_Icc
  change (∫s in Icc l h,A (R s))≤2*T
  calc
    _ ≤ ∫s in Icc l h,(Icc x y).indicator (fun _ => (2:ℝ)) s := by
      apply integral_mono (R.map A).integrable_of_isFiniteMeasure iB.integrableOn
      intro s
      change A (R s)≤(Icc x y).indicator (fun _ => (2:ℝ)) s
      by_cases m : s∈Icc x y
      · rw [indicator_of_mem m]
        unfold A IncidencePiece.rarePairPositive
        split <;> norm_num
      · rw [indicator_of_notMem m,not_not.mp (fun n => m (hs s n))]
    _ ≤ ∫s,(Icc x y).indicator (fun _ => (2:ℝ)) s := integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun _ => indicator_nonneg (fun _ _ => by norm_num) _)) iB
    _ = 2*T := by
      rw [integral_indicator_const (2:ℝ) measurableSet_Icc,Real.volume_real_Icc,hxy,max_eq_left hT,smul_eq_mul,mul_comm]

private theorem ordered_rare_charge (M : IncidencePiece K) (u : InfinitePlace K→ℝ) (v : Place K)
    (d : CoordinateLevel M.Label→M.Label) {p q r : Competition.Plane}
    (he : (p,q)∈M.E) (he' : (p,r)∈M.E) (hne : q≠r)
    (hord : M.threshold (valuation v) (p,q)≤M.threshold (valuation v) (p,r)) {l h : ℝ}
    (b : M.threshold (valuation v) (p,q)∈Icc l h) (b' : M.threshold (valuation v) (p,r)∈Icc l h) :
    recordIntegral (M.recordsAt u v) l h (M.rarePairScore d p q r)≤
      flankCharge (valuation v) (flankConstant v) (jump M p q) (jump M p r) := by
  let R := M.recordsAt u v
  let D := fun t : CoordinateLevel M.Label => |bitValue (t.bit (p,q))-bitValue (t.bit (p,r))|
  have db (s : ℝ) : D (R s)=|thresholdBit (M.threshold (valuation v) (p,q)) s-
      thresholdBit (M.threshold (valuation v) (p,r)) s| := by
    simp only [D,R,record_threshold M u v s _ he,record_threshold M u v s _ he',bitValue_decide]
  have dh : recordIntegral R l h D=M.threshold (valuation v) (p,r)-M.threshold (valuation v) (p,q) := by
    change (∫s in Icc l h,D (R s))=_
    simp_rw [db]
    rw [(threshold_difference b.1 b'.1 b.2 b'.2).2,abs_of_nonpos (sub_nonpos.mpr hord),neg_sub]
  have hp := rare_positive_integral M u v d he he' hne hord l h
  change recordIntegral R l h (M.rarePairPositive d p q r-D)≤_
  rw [map_sub,dh]
  unfold flankCharge
  change OAI.PlanarUnitDistances.BudgetPlaces.threshold (valuation v) (jump M p q) ≤
    OAI.PlanarUnitDistances.BudgetPlaces.threshold (valuation v) (jump M p r) at hord
  rw [max_eq_right hord,min_eq_left hord]
  exact sub_le_sub_right hp _

/-- The signed fixed-pair rare score exhausts at most the prescribed local
flank charge at any archimedean or finite place, including tied thresholds. -/
theorem local_rare_charge (M : IncidencePiece K) (u : InfinitePlace K→ℝ) (v : Place K)
    (d : CoordinateLevel M.Label→M.Label) {p q r : Competition.Plane}
    (he : (p,q)∈M.E) (he' : (p,r)∈M.E) (hne : q≠r) {l h : ℝ}
    (b : M.threshold (valuation v) (p,q)∈Icc l h) (b' : M.threshold (valuation v) (p,r)∈Icc l h) :
    recordIntegral (M.recordsAt u v) l h (M.rarePairScore d p q r)≤
      flankCharge (valuation v) (flankConstant v) (jump M p q) (jump M p r) := by
  rcases le_total (M.threshold (valuation v) (p,q)) (M.threshold (valuation v) (p,r)) with ord|ord
  · exact ordered_rare_charge M u v d he he' hne ord b b'
  · have h0 := ordered_rare_charge M u v d he' he hne.symm ord b' b
    have rare : M.rarePairScore d p q r=M.rarePairScore d p r q := by
      funext s
      have eq : M.rarePairPositive d p q r s=M.rarePairPositive d p r q s := by
        unfold IncidencePiece.rarePairPositive
        split_ifs with a b b
        · rfl
        · exact (b ⟨a.1,a.2.1,a.2.2.2.1,a.2.2.1,a.2.2.2.2.symm⟩).elim
        · exact (a ⟨b.1,b.2.1,b.2.2.2.1,b.2.2.1,b.2.2.2.2.symm⟩).elim
        · rfl
      simp only [rarePairScore,eq,abs_sub_comm (bitValue (s.bit (p,q))) (bitValue (s.bit (p,r)))]
    have dd : differenceProduct (jump M p q) (jump M p r)=differenceProduct (jump M p r) (jump M p q) := by
      unfold differenceProduct; ring
    rw [rare,flankCharge_eq _ _ (jump_ne M he) (jump_ne M he') (distinct_jumps M he he' hne),dd]
    exact h0.trans_eq (flankCharge_eq _ _ (jump_ne M he') (jump_ne M he) (distinct_jumps M he' he hne.symm))

end
end PlanarUnitDistances.ResearchPhysical

