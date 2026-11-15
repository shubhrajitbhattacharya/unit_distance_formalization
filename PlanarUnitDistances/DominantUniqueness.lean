import PlanarUnitDistances.PhysicalScores

namespace PlanarUnitDistances.Competition.IncidencePiece
open Finset NumberField Real
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K] {L L' : Type*}

def dominantAt (M : IncidencePiece K) (r : CoordinateLevel L) (a : L) : Prop :=
  M.pointMass (fun p => r.selected p≠a)+M.centerMass (fun q => r.selected q≠a)≤
    2*(M.minorityMass r+M.inconsistentMass r)


end
end PlanarUnitDistances.Competition.IncidencePiece
