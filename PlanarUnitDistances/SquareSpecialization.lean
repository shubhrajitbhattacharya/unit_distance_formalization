import PlanarUnitDistances.IsolatedStationaryDeformation
import PlanarUnitDistances.MaximalPolynomialHeight
import PlanarUnitDistances.SpecialFiberCoefficient

namespace PlanarUnitDistances.StationaryDeformation
open Polynomial
noncomputable section

/-- One coefficient is chosen before the component. It vanishes at every
isolated closed point of the special fiber of this square polynomial family. -/
theorem common_first_coefficient {k A ι : Type} [Field k] [CommRing A] [Fintype ι]
    (g : Fin (Fintype.card ι) → Polynomial (MvPolynomial ι k))
    (φ : A →+* MvPolynomial ι k) (H : Polynomial A) (nonzero : H ≠ 0)
    (vanishes : H.eval₂ (C.comp φ) X ∈ Ideal.span (Set.range g)) :
    ∃ d, H.coeff d ≠ 0 ∧ (∀ e < d, H.coeff e = 0) ∧
      ∀ (P : Ideal (MvPolynomial ι k)) [P.IsMaximal],
        P ∈ ((Ideal.span (Set.range g)).map (evalRingHom 0)).minimalPrimes → φ (H.coeff d) ∈ P := by
  obtain ⟨d,hd,before,descend⟩ := UniversalIncidence.first_surviving_coefficient H nonzero
  refine ⟨d,hd,before,?_⟩
  intro P _ special
  obtain ⟨Q,hQ,below,away⟩ := isolated_square_lifts _ g P special (maximal_polynomial_height (k:=k) P).ge
  let := hQ.isPrime
  let f := Ideal.Quotient.mk Q
  let ρ : Polynomial (MvPolynomial ι k) →+* (MvPolynomial ι k ⧸ P) :=
    (Ideal.Quotient.mk P).comp (evalRingHom 0)
  have killed : Q ≤ RingHom.ker ρ := fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (below hx)
  let reduce := Ideal.Quotient.lift Q ρ killed
  have zero : H.eval₂ (f.comp (C.comp φ)) (f X) = 0 :=
    (hom_eval₂ H (C.comp φ) f X).symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr (hQ.le vanishes))
  have res := descend (f.comp (C.comp φ)) reduce (f X)
    (fun h => away (Ideal.Quotient.eq_zero_iff_mem.mp h)) zero (by change (Ideal.Quotient.mk P) (Polynomial.eval 0 X) = 0; simp)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change (Ideal.Quotient.mk P) (Polynomial.eval 0 (C (φ (H.coeff d)))) = 0 at res
  simpa using res

end
end PlanarUnitDistances.StationaryDeformation
