import PlanarUnitDistances.SignedRecord
import PlanarUnitDistances.RecordBudget
import PlanarUnitDistances.ArithmeticLevels

namespace PlanarUnitDistances.Competition.IncidencePiece
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K] {L : Type*}

def rareTripleError (r : CoordinateLevel L) (a : L) {M : IncidencePiece K} (v : Triple M) :=
  r.twoEdgeError a v.1.val v.2.1.val v.2.2.val + 2*r.exceptionAt a v.1.val*r.exceptionAt a v.2.2.val

def commonBitError (M : IncidencePiece K) (r : CoordinateLevel M.Label) (v : Triple M) :=
  if eps≤M.minorityMass r then |bitValue (r.bit (v.1.val,v.2.1.val))-bitValue (r.bit (v.2.2.val,v.2.1.val))| else 0

def badWidth (M : IncidencePiece K) (r : CoordinateLevel M.Label) : ℝ :=
  if M.minorityMass r<eps ∧ eps<M.inconsistentMass r then 1 else 0

/-- This is the manuscript's Z integrand at one record for the two
actual incidences. Its three summands are the good rare error (including
the double-exception correction), common disagreement and bad width. -/
def recordError (M : IncidencePiece K) (d : CoordinateLevel M.Label → M.Label)
    (v : Triple M) (r : CoordinateLevel M.Label) :=
  M.masked (fun j => rareTripleError j (d j) v) r+M.commonBitError r v+M.badWidth r

end
end PlanarUnitDistances.Competition.IncidencePiece
