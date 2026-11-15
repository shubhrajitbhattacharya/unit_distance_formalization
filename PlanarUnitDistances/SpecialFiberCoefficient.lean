import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Div

namespace PlanarUnitDistances.UniversalIncidence
open Polynomial
noncomputable section

/-- Extract a specific coefficient of a nonzero deformation polynomial.
On an integral component where the deformation parameter is nonzero,
that coefficient vanishes at every specialization killing the parameter. -/
theorem first_surviving_coefficient {A : Type*} [CommRing A] (P : Polynomial A) (hP : P≠0) :
    ∃ n, P.coeff n≠0 ∧ (∀ m<n,P.coeff m=0) ∧
      ∀ {D S : Type} [CommRing D] [IsDomain D] [CommRing S] (φ : A →+* D) (ρ : D →+* S)
        (ε : D), ε≠0 → P.eval₂ φ ε=0 → ρ ε=0 → ρ (φ (P.coeff n))=0 := by
  obtain ⟨Q,eq,nodiv⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hP 0
  simp only [C_0,sub_zero] at eq nodiv
  let n := P.rootMultiplicity 0
  have factor : P=X^n*Q := eq
  have coeff : P.coeff n=Q.coeff 0 := by
    conv_lhs => rw [factor,coeff_X_pow_mul']
    simp
  refine ⟨n,fun h => nodiv (X_dvd_iff.mpr (coeff.symm.trans h)),?_,?_⟩
  · intro m hm
    rw [factor,coeff_X_pow_mul',ite_eq_right (Nat.not_le.mpr hm)]
  · intro D S _ _ _ φ ρ ε hε root zero
    have val : (eval₂RingHom φ ε) P=0 := root
    rw [factor,map_mul,map_pow] at val
    have positive : (eval₂RingHom φ ε) X≠0 := by simpa using hε
    have qroot := (mul_eq_zero.mp val).resolve_left (pow_ne_zero _ positive)
    have z := congrArg ρ qroot
    change ρ (Q.eval₂ φ ε)=ρ 0 at z
    rw [hom_eval₂,zero,eval₂_at_zero,ρ.map_zero] at z
    simpa only [coeff,RingHom.comp_apply] using z

end
end PlanarUnitDistances.UniversalIncidence
