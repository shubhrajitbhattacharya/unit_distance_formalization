import PlanarUnitDistances.ResearchScoreFrontier
import PlanarUnitDistances.DominantWidthMeans
import PlanarUnitDistances.OrdinaryPosteriorCollisions
import PlanarUnitDistances.GridProperness
import PlanarUnitDistances.Main
import PlanarUnitDistances.GridLocus
import PlanarUnitDistances.MovingGridAnchors
import PlanarUnitDistances.EffectiveGridGeometry
import PlanarUnitDistances.ResearchMotion
import PlanarUnitDistances.TripleSelection

namespace PlanarUnitDistances.ResearchPhysical
open OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open CommonFieldModel ProofAssembly NumberField Filter MeasureTheory
open PhysicalLevels CommonTemplate RareScore FiniteLaw FiniteStarCoupling
open UniformNormalization UniformPhysical ComparisonConstants
open scoped Topology Classical
noncomputable section
variable {P Q : Finset Competition.Plane}

abbrev originalRecordMeasure (M : Model P Q) (u : InfinitePlace M.field → ℝ) :=
  fullMeasure (unitRows P Q) M.z M.w (fun v => (u v,u v)) (fun v => (u v,u v))

/-- Quantitative data available before asking for any full score bound.
The expected point and center widths here refer to the same selected label. -/
structure OriginalScoreInputs (M : Model P Q) (he : 0 < incidences P Q)
    (u : InfinitePlace M.field → ℝ) (n : ℕ) (c : Record P Q → Finset (P⊕Q) × Finset (P⊕Q)) : Prop where
  fractional : ∀v,u v∈Set.Ioo (0:ℝ) 1
  short : n<historyDepth (unitWalkInformation P Q)
  point_degree : ∀p∈P,(2:ℝ)^144000≤degree Q p
  center_degree : ∀q∈Q,(2:ℝ)^144000≤degree P q
  list_per_degree : ∀p∈P,(Fintype.card (FullList n):ℝ)/degree Q p≤dy 144000
  scale_eq : PhysicalLevels.scale (incidenceLaw P Q he) (originalRecordMeasure M u)=pieceScale M
  large : (2:ℝ)^2100 < pieceScale M
  inconsistency_le : let π := incidenceLaw P Q he
    (∫j,inconsistency π j.bit j.x j.y ∂originalRecordMeasure M u) ≤ 4
  dominant : let π := incidenceLaw P Q he
    ∀j∈PhysicalLevels.goodRare π,pointException π (rareBit π j) (c j) j.x+
      centerException π (rareBit π j) (c j) j.y ≤ 2*(minority π j+inconsistency π j.bit j.x j.y)
  common_width_le : width (originalRecordMeasure M u) (common (incidenceLaw P Q he)) ≤ pieceScale M/dy 1800
  point_width_le : let π := incidenceLaw P Q he
    pointWidth π (originalRecordMeasure M u) (rareBit π) c ≤ 4*pieceScale M
  center_width_le : let π := incidenceLaw P Q he
    centerWidth π (originalRecordMeasure M u) (rareBit π) c ≤ 4*pieceScale M

/-- The manuscript's all-place upper bound for its center, point and
list-conditioned point experiments on the original geometric walk. -/
def OriginalTotalScoreUpper : Prop :=
  ∀ᶠ t : ℝ in atTop, ∀ (P Q : Finset Competition.Plane) (M : Model P Q), LargePiece t P Q M →
    ∀ (he : 0 < incidences P Q) (u : InfinitePlace M.field → ℝ)
      (n : ℕ) (h : P → FiniteInformation.History (Hashes×Hashes) n)
      (c : Record P Q → Finset (P⊕Q) × Finset (P⊕Q)), OriginalScoreInputs M he u n c →
       let π := incidenceLaw P Q he
       historyTotalScores (I:=Positions) π (originalRecordMeasure M u) h c

theorem moments_of_total_score_upper (upper : OriginalTotalScoreUpper) :
    ∀ᶠ t : ℝ in atTop, ∀ (P Q : Finset Competition.Plane) (M : Model P Q),
      LargePiece t P Q M → ComparisonMoments M := by
  filter_upwards [eventually_moments_of_total_scores,upper,eventual_ordinary_degrees,eventual_full_list_collision]
    with t select bound degrees lists
  intro P Q M piece
  obtain ⟨he,u,frac,hm,n,hn,h,c,dom,finish⟩ := select P Q M piece
  let π := incidenceLaw P Q he
  let ν := originalRecordMeasure M u
  have sc : PhysicalLevels.scale π ν=pieceScale M := full_scale _ _ he (unitRows_total P Q) M.z M.w _ _
  have large : (2:ℝ)^2100<pieceScale M := piece.2.2.2.2.2.2.2.2.2.2
  have four : (4:ℝ)≤PhysicalLevels.scale π ν := by
    rw [sc]
    have cmp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by decide : 2≤2100)
    norm_num1 at cmp
    exact cmp.trans large.le
  obtain ⟨xp,yq⟩ := width_means_of_dominance π ν c hm four dom
  obtain ⟨dp,dq⟩ := degrees.2 P Q M piece
  apply finish
  exact bound P Q M piece he u n h c
    ⟨frac,hn,dp,dq,(lists P Q M piece n hn).2,sc,large,hm,dom,
      by rw [←sc]; exact common_width π ν,by rwa [←sc],by rwa [←sc]⟩


end
end PlanarUnitDistances.ResearchPhysical
