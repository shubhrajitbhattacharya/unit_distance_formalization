import PlanarUnitDistances.PosteriorWidth

namespace OAI.PlanarUnitDistances.PhysicalLevels
open Finset FiniteLaw FiniteStarCoupling CommonTemplate MeasureTheory
open _root_.PlanarUnitDistances.ComparisonConstants
open scoped Classical
noncomputable section
variable {P Q I L : Type*} [Fintype P] [Fintype Q] [Fintype I] [Nonempty I] [Fintype L] [Nonempty L]

abbrev scale (π : Law (P×Q)) (ν : Measure (Record P Q)) := ∫t,minority π t ∂ν
def commonLaw (π : Law (P×Q)) (ν : Measure (Record P Q)) := ν.restrict {t | common π t}
instance (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν] :
    IsFiniteMeasure (commonLaw π ν) := by unfold commonLaw; infer_instance

lemma common_mass (π : Law (P×Q)) (ν : Measure (Record P Q)) :
    (commonLaw π ν).real Set.univ = width ν (common π) := by
  rw [commonLaw,measureReal_restrict_apply MeasurableSet.univ,Set.univ_inter,width]
  symm
  exact integral_indicator_one (Set.toFinite _).measurableSet

private lemma remove_posterior {a b u x e : ℝ} (h : a≤b+u+16*e) (hu : u≤2*x+e) :
    a≤b+2*x+17*e := by linarith

/-- Simultaneous common score inequalities with the posterior term removed.
The same history and the same restricted record law occur throughout. A null
common region is allowed. The dominant rare label may be chosen arbitrarily
in this inequality, but the width X uses exactly that choice. -/
theorem common_posterior_scores (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν]
    (hp : ∀p,0<(left π).val p) {θ : ℝ} (hθ : 0≤θ) (hpθ : ∀p,(left π).val p≤θ)
    (hpair : ∀p q : P,p≠q → (∫t,PredictionCut.pairScore (t.x p) (t.x q) ∂ν) ≤ Real.log 2)
    (hm : (∫t,inconsistency π t.bit t.x t.y ∂ν) ≤ 4) (hs : 2^2100<scale π ν)
    (K : ℕ) (hK : 0<K) (hD : 0≤commonInformation π)
    (hk : (2:ℝ)^576000*(commonInformation π+1) ≤ (K:ℝ))
    (Icard : (Fintype.card I:ℝ)=(2:ℝ)^18000) (Lcard : ((Fintype.card L:ℝ))⁻¹=dy 144000)
    (hsize : (Fintype.card L:ℝ)^(2*(K-1))*θ ≤ dy 144000) :
    ∃ n<K, ∃ h : P → FiniteInformation.History (L×L) n,
      ((∫t,cvT (I:=I) π h t ∂commonLaw π ν)+(∫t,VQ π t.bit ∂commonLaw π ν))/6 ≤
        (∫t,cdT (I:=I) π h t ∂commonLaw π ν)+(∫t,DQ π t.bit t.x ∂commonLaw π ν)+16*(dy 144*scale π ν) ∧
      ∀ (r : Record P Q → Bool) (label : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)),
      (∫t,VP π t.bit ∂commonLaw π ν)/6 ≤ (∫t,DP π t.bit t.y ∂commonLaw π ν)+
        2*pointWidth π ν r label+17*(dy 144*scale π ν) := by
  have hpos : 0≤dy 144*scale π ν := mul_nonneg (pos _).le ((pow_pos (by norm_num : (0:ℝ)<2) 2100).trans hs).le
  by_cases hnull : commonLaw π ν=0
  · refine ⟨0,hK,fun _ => PUnit.unit,?_⟩
    simp only [hnull,integral_zero_measure,add_zero,zero_div,zero_add]
    constructor
    · exact mul_nonneg (by norm_num) hpos
    · intro r label
      have hx : 0≤pointWidth π ν r label := avg_nonneg _ (fun _ => integral_nonneg (fun _ => RareScore.ind_nonneg _))
      exact add_nonneg (mul_nonneg (by norm_num) hx) (mul_nonneg (by norm_num) hpos)
  letI : NeZero (commonLaw π ν) := ⟨hnull⟩
  have hm' : (∫t,inconsistency π t.bit t.x t.y ∂commonLaw π ν)≤4 :=
    (integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall (fun _ => event_nonneg ..))
      Integrable.of_finite).trans hm
  obtain ⟨n,hn,h,_,hA,hB⟩ := exact_common_scores (I:=I) (L:=L) π hp (commonLaw π ν)
    measureReal_univ_pos id (fun _ => measurable_of_finite _) (fun _ => measurable_of_finite _)
    (fun _ _ => measurable_of_finite _) K hK hD hk Icard Lcard hs
    ((common_mass π ν).trans_le (common_width π ν)) hm'
  have nle : n≤K-1 := by omega
  have card : (Fintype.card (FiniteInformation.History (L×L) n):ℝ) ≤ (Fintype.card L:ℝ)^(2*(K-1)) := by
    rw [FiniteInformation.history_card,Fintype.card_prod]
    push_cast
    rw [←sq,←pow_mul]
    apply pow_le_pow_right₀
    · exact_mod_cast Fintype.card_pos (α:=L)
    · omega
  refine ⟨n,hn,h,hA,?_⟩
  intro r label
  have ht := posterior_comparison π ν h r label hpair hθ hpθ
    ((mul_le_mul_of_nonneg_right card hθ).trans hsize) hm hs
  have ht' : (∫t,posteriorMoment π h t ∂commonLaw π ν)≤2*pointWidth π ν r label+dy 144*scale π ν := by
    unfold commonLaw
    rw [←integral_indicator (Set.toFinite _).measurableSet]
    exact ht
  exact remove_posterior hB ht'

end
end OAI.PlanarUnitDistances.PhysicalLevels
