import Mathlib

/-! Push a square-root relation through specialization, including singular
fibres. The degree of the norm doubles, with degree two for the root. -/
namespace PlanarUnitDistances.RadicalNorm
open MvPolynomial
noncomputable section

theorem norm_specializes {R S : Type*} [CommRing R] [CommRing S] {d : R}
    (f : R →+* S) (r : S) (hr : r^2=f d) (z : QuadraticAlgebra R d 0) :
    f z.norm=(f z.re+f z.im*r)*(f z.re-f z.im*r) := by
  simp only [QuadraticAlgebra.norm_def,zero_mul,add_zero,map_sub,map_mul]
  linear_combination (f z.im)^2 * hr


end
end PlanarUnitDistances.RadicalNorm
