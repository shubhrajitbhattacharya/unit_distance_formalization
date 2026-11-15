import PlanarUnitDistances.ResearchMomentConclusion
import PlanarUnitDistances.ResearchExceptionalIntegral
import PlanarUnitDistances.ResearchCommonMeasure
import PlanarUnitDistances.GeometricRareLaw
import PlanarUnitDistances.DenseScores
import PlanarUnitDistances.FullScoreComparison
import PlanarUnitDistances.FullHistoryLists

namespace PlanarUnitDistances.ResearchPhysical
open OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open CommonFieldModel ProofAssembly NumberField Filter MeasureTheory
open PhysicalLevels CommonTemplate RareScore FiniteLaw FiniteStarCoupling
open UniformNormalization UniformPhysical ComparisonConstants
open scoped Topology Classical
noncomputable section

/-- All three literal upper estimates for the list of iid history values.
Keeping its index type polymorphic avoids evaluating the huge finite list. -/
def historyTotalScores {P Q I H : Type*} [Fintype P] [Fintype Q] [Fintype I] [Fintype H] [Nonempty I]
    (π : Law (P×Q)) (ν : Measure (Record P Q)) (h : P → H)
    (c : Record P Q → Finset (P⊕Q) × Finset (P⊕Q)) : Prop :=
  TotalScoreComparison π ν (listLaw (I:=I) π h) c

/-- The manuscript's three common-level comparisons with the same iid
history list and the same local dominant rule as the score hypothesis. -/
def historyThreeBounds {P Q I H : Type*} [Fintype P] [Fintype Q] [Fintype I] [Fintype H] [Nonempty I]
    (π : Law (P×Q)) (ν : Measure (Record P Q)) (h : P → H)
    (c : Record P Q → Finset (P⊕Q) × Finset (P⊕Q)) : Prop :=
  ThreeComparisonBounds π ν (listLaw (I:=I) π h) c

private theorem label_for_history {P Q I H : Type*} [Fintype P] [Fintype Q] [Fintype I] [Fintype H] [Nonempty I]
    (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν] (h : P → H) {ξ : ℝ}
    (R : RectangleLaw π ξ) (hξ : 0≤ξ) (hsξ : ξ≤dy 146)
    (hm : (∫j,inconsistency π j.bit j.x j.y ∂ν)≤4) (hs : 2^2100<PhysicalLevels.scale π ν)
    (first : ((∫j,cvT (I:=I) π h j ∂commonLaw π ν)+(∫j,VQ π j.bit ∂commonLaw π ν))/6 ≤
      (∫j,cdT (I:=I) π h j ∂commonLaw π ν)+(∫j,DQ π j.bit j.x ∂commonLaw π ν)+16*(dy 144*PhysicalLevels.scale π ν))
    (second : ∀c,(∫j,VP π j.bit ∂commonLaw π ν)/6 ≤ (∫j,DP π j.bit j.y ∂commonLaw π ν)+
      2*pointWidth π ν (rareBit π) c+17*(dy 144*PhysicalLevels.scale π ν)) :
    ∃ c : Record P Q → Finset (P⊕Q)×Finset (P⊕Q),
      (∀j∈PhysicalLevels.goodRare π,pointException π (rareBit π j) (c j) j.x+
        centerException π (rareBit π j) (c j) j.y≤2*(minority π j+inconsistency π j.bit j.x j.y)) ∧
      (historyTotalScores (I:=I) π ν h c → PhysicalLevels.scale π ν/203 < pointWidth π ν (rareBit π) c ∧
        (∫j,VQ π j.bit ∂commonLaw π ν) ≤ 2048*(dy 144*PhysicalLevels.scale π ν) ∧
        historyThreeBounds (I:=I) π ν h c) :=
  exists_label_for_all_score_bounds π ν (listLaw (I:=I) π h) R hξ hsξ hm hs first second

/-- On the original unit-incidence model, choose the common shifts, then
one prediction history, then a dominant rule, all before requiring the
three full score inequalities. Those inequalities imply all the original
comparison moments on the very same incidence piece. -/
theorem eventually_moments_and_comparisons :
    ∀ᶠ t : ℝ in atTop, ∀ (P Q : Finset Competition.Plane) (M : Model P Q), LargePiece t P Q M →
      ∃ (he : 0 < incidences P Q) (u : InfinitePlace M.field → ℝ),
        (∀v,u v∈Set.Ioo (0:ℝ) 1) ∧
        let π := incidenceLaw P Q he
        let ν := fullMeasure (unitRows P Q) M.z M.w (fun v => (u v,u v)) (fun v => (u v,u v))
        (∫j,inconsistency π j.bit j.x j.y ∂ν) ≤ 4 ∧
        ∃ n < historyDepth (unitWalkInformation P Q), ∃ h : P → FiniteInformation.History (Hashes×Hashes) n,
        ∃ c : Record P Q → Finset (P⊕Q) × Finset (P⊕Q),
          (∀j∈PhysicalLevels.goodRare π,pointException π (rareBit π j) (c j) j.x+
            centerException π (rareBit π j) (c j) j.y ≤ 2*(minority π j+inconsistency π j.bit j.x j.y)) ∧
          (historyTotalScores (I:=Positions) π ν h c → ComparisonMoments M ∧
            historyThreeBounds (I:=Positions) π ν h c) := by
  have gp : 0 < Competition.savingG := by unfold Competition.savingG; positivity [exactGap_pos]
  have decay : Tendsto (fun t : ℝ => t^(-150*Competition.savingG)) atTop (nhds 0) := by
    simpa only [neg_mul] using tendsto_rpow_neg_atTop (show 0 < 150*Competition.savingG by positivity)
  filter_upwards [eventually_two_comparisons,common_scores_on_large_piece,eventually_gt_atTop (0:ℝ),
    decay.eventually (eventually_le_nhds (pos 146))] with t two histories ht hsmall
  intro P Q M piece
  have history := histories P Q M piece
  obtain ⟨u,d,hu,hd,_,hmis,_,_,finish⟩ := two P Q M piece
  obtain ⟨_,plo,_,_,edge,degP,_,degQ,rect,_,big⟩ := piece
  have he : 0 < incidences P Q := (Real.rpow_pos_of_pos ht _).trans_le edge
  let π := incidenceLaw P Q he
  let U := fun v => (u v,u v)
  let ν := fullMeasure (unitRows P Q) M.z M.w U U
  have hm : (∫j,inconsistency π j.bit j.x j.y ∂ν) ≤ 4 := by
    rw [←inconsistency_integral_eq M he u]
    exact hmis.trans (by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)])
  have mp := (Real.rpow_pos_of_pos ht _).trans_le plo
  have qp := pos_of_mul_pos_right (he.trans_le (incidences_le P Q)) (Nat.cast_nonneg _)
  have hq (q : Q) : 0 < degree P q :=
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos ht _)).trans_le (degQ q q.prop).1
  have cut : RectangleLaw π (t^(-150*Competition.savingG)) :=
    incidence_rectangles P Q mp qp he (fun p hp => (degP p hp).2.2.1)
      (fun q hq => (degQ q hq).2.2) rect
  have sc : PhysicalLevels.scale π ν=pieceScale M :=
    full_scale _ _ he (unitRows_total P Q) M.z M.w U U
  have large : 2^2100 < PhysicalLevels.scale π ν := sc ▸ big
  obtain ⟨n,hn,h,first,second⟩ := history he U U hm
  obtain ⟨c,dom,score⟩ := label_for_history (I:=Positions) π ν h cut (Real.rpow_nonneg ht.le _)
    hsmall hm large (by rw [sc]; exact first) (fun l => by rw [sc]; exact second (rareBit π) l)
  refine ⟨he,u,hu,hm,n,hn,h,c,dom,?_⟩
  intro full
  obtain ⟨width,common,triple⟩ := score full
  rw [sc] at width common
  refine ⟨?_,triple⟩
  apply finish
  · rw [exceptional_point_mean_eq M he u d c hd dom]
    exact width
  · rw [common_integral_eq M he hq u U U]
    have same : dy 144=(2:ℝ)^(-144:ℝ) := by norm_num [dy,Real.rpow_neg]
    rw [same] at common
    linarith only [common]

theorem eventually_moments_of_total_scores :
    ∀ᶠ t : ℝ in atTop, ∀ (P Q : Finset Competition.Plane) (M : Model P Q), LargePiece t P Q M →
      ∃ (he : 0 < incidences P Q) (u : InfinitePlace M.field → ℝ),
        (∀v,u v∈Set.Ioo (0:ℝ) 1) ∧
        let π := incidenceLaw P Q he
        let ν := fullMeasure (unitRows P Q) M.z M.w (fun v => (u v,u v)) (fun v => (u v,u v))
        (∫j,inconsistency π j.bit j.x j.y ∂ν) ≤ 4 ∧
        ∃ n < historyDepth (unitWalkInformation P Q), ∃ h : P → FiniteInformation.History (Hashes×Hashes) n,
        ∃ c : Record P Q → Finset (P⊕Q) × Finset (P⊕Q),
          (∀j∈PhysicalLevels.goodRare π,pointException π (rareBit π j) (c j) j.x+
            centerException π (rareBit π j) (c j) j.y ≤ 2*(minority π j+inconsistency π j.bit j.x j.y)) ∧
          (historyTotalScores (I:=Positions) π ν h c → ComparisonMoments M) := by
  filter_upwards [eventually_moments_and_comparisons] with t all
  intro P Q M piece
  obtain ⟨he,u,frac,hm,n,hn,h,c,dom,finish⟩ := all P Q M piece
  exact ⟨he,u,frac,hm,n,hn,h,c,dom,fun upper => (finish upper).1⟩

end
end PlanarUnitDistances.ResearchPhysical
