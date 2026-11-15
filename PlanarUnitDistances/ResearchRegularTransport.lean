import PlanarUnitDistances.ResearchPhysicalModel
import PlanarUnitDistances.ProofAssembly
import PlanarUnitDistances.ResearchIncidenceCounts

namespace PlanarUnitDistances.ResearchPhysical
open OAI.PlanarUnitDistances CommonFieldModel OAI.PlanarUnitDistances.CircleIncidence
open Competition.IncidencePiece.Research
noncomputable section
variable {P Q : Finset Competition.Plane}

/-- All regularity bounds on the original piece survive conversion to the
explicit-edge data type, on the same P, Q, field, coordinates and edge law. -/
theorem regular_of_large_piece (M : Model P Q) (t : ℝ) (hl : ProofAssembly.LargePiece t P Q M) :
    Competition.Regular (toPiece M) t := by
  obtain ⟨_,hm,hM,hn,he,hp,_,hq,hrect,hI,_⟩ := hl
  exact regular_of_estimates (toPiece M) (full M) t hm hM hn he hp hq hrect hI

end
end PlanarUnitDistances.ResearchPhysical

