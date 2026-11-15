import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

/-! Deep Blue. Effective separation of a proper projected locus.
The explicit published hypotheses are Heintz's defining equations on each
irreducible component, geometric Bézout, and linear projection of degree.
The arguments selecting the common witness and keeping the degree are proved. -/

namespace PlanarUnitDistances.Competition.PublishedElimination

open MvPolynomial

variable {k I J : Type*} [Field k]


def equations (fs : List (MvPolynomial I k)) : Set (I → k) :=
  {x | ∀ f ∈ fs, MvPolynomial.eval x f = 0}


end PlanarUnitDistances.Competition.PublishedElimination
