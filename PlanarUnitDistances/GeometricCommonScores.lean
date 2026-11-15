import PlanarUnitDistances.UniformPhysical
import PlanarUnitDistances.RecordComparison
import PlanarUnitDistances.PhysicalLevels

namespace PlanarUnitDistances.UniformPhysical
open Finset MeasureTheory NumberField OAI.PlanarUnitDistances
open FiniteLaw FiniteStarCoupling CommonTemplate PhysicalLevels StateConsistency
open UniformNormalization BoundedHeight ComparisonConstants
open scoped Classical
noncomputable section
variable {P Q I L : Type} [Fintype P] [Fintype Q] [Fintype I] [Nonempty I] [Fintype L] [Nonempty L]
variable {K : Type*} [Field K] [NumberField K]

/-- For any prescribed pair of shifts whose total inconsistency is at most four,
the same finite history gives both common-level score estimates. -/
theorem graph_common_scores_at (rows : Q → Finset P) (e : ℝ) (he : 0<e) (ht : ∑q,((rows q).card:ℝ)=e)
    (hrows : ∀q,(rows q).Nonempty) (hcols : ∀p,(pointCenters rows p).Nonempty)
    (z w : P⊕Q → K) (hz : Function.Injective (z ∘ Sum.inl)) (hw : Function.Injective (w ∘ Sum.inl))
    {θ : ℝ} (hθ : 0≤θ) (hatom : ∀p,((pointCenters rows p).card:ℝ)/e≤θ)
    (N : ℕ) (hN : 0<N) (hD : 0≤twoEdgeInformation rows e)
    (hN' : (2:ℝ)^576000*(twoEdgeInformation rows e+1) ≤ (N:ℝ))
    (Icard : (Fintype.card I:ℝ)=(2:ℝ)^18000) (Lcard : ((Fintype.card L:ℝ))⁻¹=dy 144000)
    (hsize : (Fintype.card L:ℝ)^(2*(N-1))*θ≤dy 144000)
    (hS : 2^2100<profileScale rows e z (fun v => -profileRadius rows z w v) (profileRadius rows z w))
    (U V : InfinitePlace K → ℝ × ℝ) :
    let π := edgeLaw rows e he ht
    let S := profileScale rows e z (fun v => -profileRadius rows z w v) (profileRadius rows z w)
    let ν := fullMeasure rows z w U V
    (∫t,inconsistency π t.bit t.x t.y ∂ν)≤4 →
      ∃ n<N, ∃ h : P → FiniteInformation.History (L×L) n,
      ((∫t,cvT (I:=I) π h t ∂commonLaw π ν)+(∫t,VQ π t.bit ∂commonLaw π ν))/6 ≤
        (∫t,cdT (I:=I) π h t ∂commonLaw π ν)+(∫t,DQ π t.bit t.x ∂commonLaw π ν)+16*(dy 144*S) ∧
      ∀ (r : Record P Q → Bool) (l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)),
      (∫t,VP π t.bit ∂commonLaw π ν)/6 ≤ (∫t,DP π t.bit t.y ∂commonLaw π ν)+
        2*pointWidth π ν r l+17*(dy 144*S) := by
  let π := edgeLaw rows e he ht
  let R := profileRadius rows z w
  dsimp only
  intro hem
  let ν := fullMeasure rows z w U V
  have hi : commonInformation π=twoEdgeInformation rows e := edge_information rows e he ht hrows
  have hs : scale π ν=profileScale rows e z (fun v => -R v) R := full_scale rows e he ht z w _ _
  have cp (p : P) : 0<(FiniteStarCoupling.left π).val p := by
    rw [edge_left]; exact div_pos (Nat.cast_pos.mpr (card_pos.mpr (hcols p))) he
  have ca (p : P) : (FiniteStarCoupling.left π).val p≤θ := (edge_left rows e he ht p).trans_le (hatom p)
  have pair (p q : P) (hn : p≠q) := full_off_diagonal rows z w hz hw U V hn
  have joint := common_posterior_scores (I:=I) (L:=L) π ν cp hθ ca pair hem
    (hs.symm ▸ hS) N hN (hi.symm ▸ hD) (hi.symm ▸ hN') Icard Lcard hsize
  rwa [hs] at joint


end
end PlanarUnitDistances.UniformPhysical
