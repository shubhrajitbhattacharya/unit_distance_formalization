import PlanarUnitDistances.ConstructiblePositions

/-! Univariate equations for finite fibers of a fixed constructible relation.
The finite set of polynomials is chosen before any parameter value. -/

namespace PlanarUnitDistances.ArithmeticIntersection
open MvPolynomial Finset
open scoped Classical
noncomputable section
variable {k A : Type*} [Field k]

/-- Retain the output coordinate and specialize the parameters. -/
def outputPolynomial (a : A → k) :
    MvPolynomial (Option A) k →+* Polynomial k :=
  eval₂Hom Polynomial.C (fun j => j.elim Polynomial.X (fun i => Polynomial.C (a i)))


end
end PlanarUnitDistances.ArithmeticIntersection
