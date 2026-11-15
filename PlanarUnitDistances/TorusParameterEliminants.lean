import PlanarUnitDistances.UniformFiberEliminants
import PlanarUnitDistances.CriticalLocus
import PlanarUnitDistances.EliminantHeight
import PlanarUnitDistances.KPSStationary

namespace PlanarUnitDistances.TorusCritical
open MvPolynomial CriticalLocus ArithmeticIntersection
open scoped Classical
noncomputable section
variable {k I J : Type*} [Field k] [Fintype I] [Fintype J]

abbrev RatioParameters (I J : Type*) := (I × Option J) × Bool

def ratioParameterValues (a : I → Option J → kˣ) (s : RatioParameters I J) : k :=
  if s.2 then ↑((a s.1.1 s.1.2)⁻¹) else ↑(a s.1.1 s.1.2)


end
end PlanarUnitDistances.TorusCritical
