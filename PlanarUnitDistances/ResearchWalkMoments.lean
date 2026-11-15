import PlanarUnitDistances.ActualPosteriorUpper
import PlanarUnitDistances.TotalScoreAssembly
import PlanarUnitDistances.ExactFromTotalScores
import PlanarUnitDistances.CollisionErrors

namespace PlanarUnitDistances.ResearchPhysical
open NumberField Filter MeasureTheory Finset OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open PhysicalLevels RareScore CommonTemplate FiniteLaw FiniteStarCoupling TemplateCoupling CommonFieldModel
open UniformNormalization UniformPhysical ComparisonConstants ProofAssembly
open scoped Topology Classical
noncomputable section

private theorem history_scores_of_cardinal :
    ∀ᶠ t : ℝ in atTop, ∀ (P Q : Finset Competition.Plane) (M : Model P Q), LargePiece t P Q M →
      ∀ (he : 0 < incidences P Q) (u : InfinitePlace M.field → ℝ) (n : ℕ)
        (c : Record P Q → Finset (P⊕Q) × Finset (P⊕Q)), OriginalScoreInputs M he u n c →
      ∀ {I H : Type} [Fintype I] [Fintype H] [Nonempty I] (h : P → H),
        (∀ p ∈ P, (Fintype.card (I → H):ℝ)/degree Q p ≤ dy 144000) →
        historyTotalScores (I:=I) (incidenceLaw P Q he) (originalRecordMeasure M u) h c := by
  filter_upwards [collision_errors_of_cardinal] with t collisions
  intro P Q M piece he u n c inputs I H _ _ _ h cap
  let π := incidenceLaw P Q he
  let U : InfinitePlace M.field → ℝ×ℝ := fun v => (u v,u v)
  let ν := originalRecordMeasure M u
  let a := listLaw (I:=I) π h
  let W := width ν (PhysicalLevels.common π)
  let X (p : P) := baseExceptionWidth π ν c (.inl p)
  let Y (q : Q) := baseExceptionWidth π ν c (.inr q)
  have step := collisions P Q M piece he a cap X Y W
    (integral_nonneg (fun _ => ind_nonneg _)) inputs.common_width_le
    (fun _ => integral_nonneg (fun _ => ind_nonneg _)) (fun _ => integral_nonneg (fun _ => ind_nonneg _))
    inputs.point_width_le inputs.center_width_le
  obtain ⟨qd,pd,td⟩ := step
  change TotalScoreComparison π ν a c
  apply total_of_base_bounds π ν a c
  · exact fun q hq => center_posterior_upper M he q hq c U U
  · exact fun p hp => point_posterior_upper M he p hp c U U
  · exact fun j p hp => template_posterior_upper M he a j p hp c U U
  · rw [inputs.scale_eq]; exact qd
  · rw [inputs.scale_eq]; exact pd
  · rw [inputs.scale_eq]; exact td

private theorem cardinal_bound_change_instance {T : Type} {i j : Fintype T} {d b : ℝ}
    (cap : (@Fintype.card T i : ℝ)/d ≤ b) : (@Fintype.card T j : ℝ)/d ≤ b := by
  cases Subsingleton.elim i j
  exact cap

/-- Every original large piece satisfies all three integrated upper score
bounds with the manuscript's coefficient 1/15 and loss 2⁻¹⁴⁴ S. -/
theorem original_total_score_upper : OriginalTotalScoreUpper := by
  filter_upwards [history_scores_of_cardinal] with t scores
  intro P Q M piece he u n h c inputs
  apply scores P Q M piece he u n c inputs (I:=Positions) h
  intro p hp
  exact cardinal_bound_change_instance (T:=FullList n) (inputs.list_per_degree p hp)

/-- The three moment bounds and both endpoint estimates on the original
common-center walk, uniformly on every sufficiently large piece. -/
theorem original_walk_moments :
    ∀ᶠ t : ℝ in atTop, ∀ (P Q : Finset Competition.Plane) (M : Model P Q),
      LargePiece t P Q M → ComparisonMoments M :=
  moments_of_total_score_upper original_total_score_upper


end
end PlanarUnitDistances.ResearchPhysical
