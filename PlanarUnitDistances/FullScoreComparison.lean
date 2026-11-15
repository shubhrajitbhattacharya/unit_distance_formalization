import PlanarUnitDistances.MinorityIntegral
import PlanarUnitDistances.RecordComparison

namespace OAI.PlanarUnitDistances.PhysicalLevels
open FiniteLaw FiniteStarCoupling CommonTemplate RareScore TemplateCoupling MeasureTheory
open _root_.PlanarUnitDistances.ComparisonConstants
open scoped Classical
noncomputable section
variable {P Q T : Type*} [Fintype P] [Fintype Q] [Fintype T]

/-- The three experiments on a single measure of physical records. The
conditional experiment uses the same list kernel in its two slots. -/
structure TotalScoreComparison (π : Law (P×Q)) (ν : Measure (Record P Q))
    (a : Q → Law T) (l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)) : Prop where
  /-- Weighted common disagreement and score for the center experiment. -/
  center : (∫t,DQ π t.bit t.x ∂commonLaw π ν)+
    rareIntegral π ν (fun t => centerScore π (rareBit π t) (l t) t.x t.y t.bit) (fun t => VQ π t.bit)
      ≤ (∫t,VQ π t.bit ∂commonLaw π ν)/15+dy 144*scale π ν
  /-- Ordinary point experiment. -/
  point : (∫t,DP π t.bit t.y ∂commonLaw π ν)+
    rareIntegral π ν (fun t => pointScore π (rareBit π t) (l t) t.x t.y t.bit) (fun t => VP π t.bit)
      ≤ (∫t,VP π t.bit ∂commonLaw π ν)/15+dy 144*scale π ν
  /-- Point experiment conditioned on the center's list. -/
  conditional : (∫t,avg (templates π a) (fun u => DP (slice π a u) t.bit t.y) ∂commonLaw π ν)+
    rareIntegral π ν (fun t => avg (templates π a) (fun u => pointScore (slice π a u) (rareBit π t)
        (l t) t.x t.y t.bit)) (fun t => avg (templates π a) (fun u => VP (slice π a u) t.bit))
      ≤ (∫t,avg (templates π a) (fun u => VP (slice π a u) t.bit) ∂commonLaw π ν)/15+dy 144*scale π ν

/-- The three conclusions of the manuscript's finite comparisons,
including the disagreement conditional on the actual list. -/
structure ThreeComparisonBounds (π : Law (P×Q)) (ν : Measure (Record P Q))
    (a : Q → Law T) (l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)) : Prop where
  center_list : (∫t,VQ π t.bit ∂commonLaw π ν)+
    (∫t,avg (templates π a) (fun u => VP (slice π a u) t.bit) ∂commonLaw π ν) ≤ 2048*(dy 144*scale π ν)
  widths : centerWidth π ν (rareBit π) l ≤ pointWidth π ν (rareBit π) l+2048*(dy 144*scale π ν)
  point : (∫t,VP π t.bit ∂commonLaw π ν) ≤ 20*centerWidth π ν (rareBit π) l+1024*(dy 144*scale π ν)

/-- Two target inequalities on the actual common center-disagreement and
rare point widths. The common-score selection and estimates for the
full score must concern the same edge law, list and rare labels. -/
theorem exists_label_for_all_score_bounds (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν]
    (a : Q → Law T) {ξ : ℝ} (R : RectangleLaw π ξ) (hξ : 0≤ξ) (hsξ : ξ≤dy 146)
    (hm : (∫t,inconsistency π t.bit t.x t.y ∂ν)≤4) (hs : 2^2100<scale π ν)
    (common₁ : ((∫t,avg (templates π a) (fun u => VP (slice π a u) t.bit) ∂commonLaw π ν)+
      (∫t,VQ π t.bit ∂commonLaw π ν))/6 ≤
      (∫t,avg (templates π a) (fun u => DP (slice π a u) t.bit t.y) ∂commonLaw π ν)+
        (∫t,DQ π t.bit t.x ∂commonLaw π ν)+16*(dy 144*scale π ν))
    (common₂ : ∀ l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q),
      (∫t,VP π t.bit ∂commonLaw π ν)/6 ≤ (∫t,DP π t.bit t.y ∂commonLaw π ν)+
          2*pointWidth π ν (rareBit π) l+17*(dy 144*scale π ν)) :
    ∃ l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q),
      (∀t∈goodRare π,pointException π (rareBit π t) (l t) t.x+
        centerException π (rareBit π t) (l t) t.y≤2*(minority π t+inconsistency π t.bit t.x t.y)) ∧
      (TotalScoreComparison π ν a l → scale π ν/203 < pointWidth π ν (rareBit π) l ∧
      (∫t,VQ π t.bit ∂commonLaw π ν) ≤ 2048*(dy 144*scale π ν) ∧ ThreeComparisonBounds π ν a l) := by
  obtain ⟨l,dom,budget⟩ := rare_error_budget π ν R hξ hsξ hm hs
  refine ⟨l,dom,?_⟩
  intro full
  obtain ⟨qu,pu,tu⟩ := full
  obtain ⟨ql,pl,tl⟩ := rare_integrals π ν a (rareBit π) l hm
  rw [pointWidth_integral,centerWidth_integral] at ql pl tl
  let e := dy 144*scale π ν
  let cq := ∫t,VQ π t.bit ∂commonLaw π ν
  let ct := ∫t,avg (templates π a) (fun u => VP (slice π a u) t.bit) ∂commonLaw π ν
  let cp := ∫t,VP π t.bit ∂commonLaw π ν
  let X := pointWidth π ν (rareBit π) l
  let Y := centerWidth π ν (rareBit π) l
  have en : 0≤e := mul_nonneg (pos _).le ((pow_pos (by norm_num : (0:ℝ)<2) 2100).trans hs).le
  have cn : 0≤ct := integral_nonneg (fun _ => avg_nonneg _ (fun _ => avg_nonneg _ (fun _ =>
    StarScore.variation_nonneg ..)))
  have dql : -cq ≤ ∫t,DQ π t.bit t.x ∂commonLaw π ν := by
    change -(∫t,VQ π t.bit ∂commonLaw π ν) ≤ _
    rw [←integral_neg]
    exact integral_mono Integrable.of_finite Integrable.of_finite (fun t => dq_lower π t.bit t.x)
  have qt : cq+ct≤2048*e := by
    dsimp only [e,cq,ct] at *
    linarith only [common₁,qu,tu,ql,tl,budget,en]
  have q : cq≤2048*e := by linarith only [qt,cn]
  have y : Y≤X+2048*e := by
    dsimp only [e,cq,X,Y] at *
    linarith only [qu,ql,budget,q,dql,en]
  have p : cp≤20*Y+1024*e := by
    have c := common₂ l
    dsimp only [e,cp,Y] at *
    linarith only [c,pu,pl,budget,en]
  have ξ100 : ξ≤1/(2:ℝ)^100 := by simpa only [dy,one_div] using hsξ.trans (antitone (by decide : 100≤146))
  exact ⟨point_width_gt_of_comparisons π ν R hξ ξ100 hm hs l q y p,q,qt,y,p⟩


end
end OAI.PlanarUnitDistances.PhysicalLevels
