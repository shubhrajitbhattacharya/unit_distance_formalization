import PlanarUnitDistances.GeometricCommonScores
import PlanarUnitDistances.ExactHistorySize
import PlanarUnitDistances.ProofAssembly

namespace PlanarUnitDistances.UniformPhysical
open Filter Finset MeasureTheory NumberField OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open FiniteLaw FiniteStarCoupling CommonTemplate PhysicalLevels StateConsistency ComparisonConstants BoundedHeight UniformNormalization
open scoped Classical Topology
noncomputable section

abbrev Positions := Fin (2^18000)
abbrev Hashes := Fin (2^144000)


/-- On each original large piece, fixing the geometry and the two archimedean
shifts before choosing the history gives the simultaneous comparison estimates. -/
theorem common_scores_on_large_piece :
    ∀ᶠ t : ℝ in atTop, ∀ (P Q : Finset Plane) (M : CommonFieldModel.Model P Q),
    ProofAssembly.LargePiece t P Q M → ∀ (he : 0 < incidences P Q)
      (U V : InfinitePlace M.field → ℝ × ℝ),
    let rows := unitRows P Q
    let π := edgeLaw rows (incidences P Q) he (unitRows_total P Q)
    let R := profileRadius rows M.z M.w
    let S := profileScale rows (incidences P Q) M.z (fun v => -R v) R
    let N := historyDepth (unitWalkInformation P Q)
    let ν := fullMeasure rows M.z M.w U V
    (∫t,inconsistency π t.bit t.x t.y ∂ν)≤4 →
      ∃ n<N, ∃ h : P → FiniteInformation.History (Hashes×Hashes) n,
        ((∫t,cvT (I:=Positions) π h t ∂commonLaw π ν)+(∫t,VQ π t.bit ∂commonLaw π ν))/6 ≤
          (∫t,cdT (I:=Positions) π h t ∂commonLaw π ν)+(∫t,DQ π t.bit t.x ∂commonLaw π ν)+16*(dy 144*S) ∧
        ∀ (r : Record P Q → Bool) (l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)),
        (∫t,VP π t.bit ∂commonLaw π ν)/6 ≤ (∫t,DP π t.bit t.y ∂commonLaw π ν)+
          2*pointWidth π ν r l+17*(dy 144*S) := by
  have small := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).eventually
    (eventually_le_nhds (pos 144000))
  filter_upwards [eventually_ge_atTop (1:ℝ),small] with t ht hsmall
  intro P Q M piece he U V
  obtain ⟨_,_,_,_,_,degreeP,hθ,degreeQ,_,info,scaleBig⟩ := piece
  have ht' : 0<t := zero_lt_one.trans_le ht
  let rows := unitRows P Q
  have deg (q : Plane) (hq : q∈Q) : 0<degree P q :=
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos ht' _)).trans_le (degreeQ q hq).1
  have nonempty (q : Q) : (rows q).Nonempty := card_pos.mp (Nat.cast_pos.mp
    ((unitRows_center_degree P Q q).symm ▸ deg q q.prop))
  have nonempty' (p : P) : (pointCenters rows p).Nonempty := by
    have dpos : 0<degree Q p := (mul_pos (by norm_num) (Real.rpow_pos_of_pos ht' _)).trans_le (degreeP p p.prop).1
    exact card_pos.mp (Nat.cast_pos.mp ((unitRows_point_degree P Q p).symm ▸ dpos))
  have ident := unitRows_information P Q deg
  let D := unitWalkInformation P Q
  have hD : 0≤D := (twoEdgeInformation_nonneg rows nonempty he (unitRows_total P Q)).trans_eq ident.symm
  have atom (p : P) : ((pointCenters rows p).card:ℝ)/incidences P Q ≤ t^(-1:ℝ) := by
    rw [unitRows_point_degree]; exact (degreeP p p.prop).2.2.2.trans hθ
  have iD : D+1≤30600*exactGap*Real.log t := by convert info using 1 <;> ring
  have col := (history_atom ht hD iD (le_rfl : t^(-1:ℝ)≤_)).trans hsmall
  have ip : (Fintype.card Positions:ℝ)=(2:ℝ)^18000 := by simp only [Positions,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  have hp : (Fintype.card Hashes:ℝ)=(2:ℝ)^144000 := by simp only [Hashes,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  have hp' : (Fintype.card Hashes:ℝ)⁻¹=dy 144000 := congrArg Inv.inv hp
  apply graph_common_scores_at (I:=Positions) (L:=Hashes) rows (incidences P Q) he (unitRows_total P Q)
      nonempty nonempty' M.z M.w M.point_injective M.wpoint_injective
      (Real.rpow_nonneg ht'.le _) atom
      (historyDepth D) (historyDepth_pos D hD) (hD.trans_eq ident) _ ip hp' _ scaleBig U V
  · rw [←ident]; exact historyDepth_large D
  · rw [hp]; exact col
  

end
end PlanarUnitDistances.UniformPhysical
