import PlanarUnitDistances.ResearchLocalWidth
import PlanarUnitDistances.TripleSelection

namespace PlanarUnitDistances.ResearchPhysical
open OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open OAI.PlanarUnitDistances.ThresholdProfiles CommonFieldModel Finset MeasureTheory
open UniformNormalization EdgeHeightScale NumberField ProofAssembly
open scoped Classical
noncomputable section
variable {P Q : Finset Competition.Plane}

/-- The scale in the all-place moment calculation is exactly the large
height S in the original manuscript, including its finite-place weights. -/
theorem scale_eq (M : Model P Q) (he : 0 < incidences P Q) : (toPiece M).scale=pieceScale M := by
  unfold Competition.IncidencePiece.scale pieceScale profileScale placeSum
  apply congrArg (fun u : ℝ => u / Module.finrank ℚ M.field)
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro v _
    exact congrArg (fun z : ℝ => (v.mult : ℝ)*z) (local_width_eq M he v.1)
  · apply congrArg finsum
    exact funext (fun v : FinitePlace M.field => local_width_eq M he v.1)

end
end PlanarUnitDistances.ResearchPhysical
