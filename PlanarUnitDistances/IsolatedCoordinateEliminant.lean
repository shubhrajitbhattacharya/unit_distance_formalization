import PlanarUnitDistances.ConcreteSquareElimination
import PlanarUnitDistances.SquareSpecialization

namespace PlanarUnitDistances.UniversalIncidence
open HomogeneousMacaulay MvPolynomial
noncomputable section

theorem root_of_test_mem {q : ℕ} {k : Type*} [Field k] (M : Ideal (State q k)) [M.IsPrime]
    (j : Fin q) (c : k) (assigned : X j-C c∈M) (p : Polynomial k) (vanishes : outputTest j p∈M) :
    p.IsRoot c := by
  let π := Ideal.Quotient.mk M
  let f := π.comp (C : k →+* State q k)
  have point : π (X j)=f c := sub_eq_zero.mp (by
    change π (X j)-π (C c)=0
    rw [←map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr assigned)
  have acts : π.comp (outputTest j)=f.comp (Polynomial.evalRingHom c) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [outputTest,f]
    · simpa [outputTest] using point
  have z : (π.comp (outputTest j)) p=0 := Ideal.Quotient.eq_zero_iff_mem.mpr vanishes
  rw [acts] at z
  exact f.injective (z.trans f.map_zero.symm)

/-- Every supplied generator satisfying these two interface properties
gives the same coefficient for all isolated points of a fixed system. -/
theorem isolated_coordinate_from_relation {q : ℕ} (F : BlockMacaulay.Universal q)
    (rel : incidenceMap F=0) (divides : F ∣ universalDeterminant q) (k : Type) [Field k] (j : Fin q)
    (Q : Fin q → MvPolynomial (Coord q) k) (hom : ∀i,(Q i).IsHomogeneous 2) :
    let H := Polynomial.Bivariate.swap (deformationMap (inputCoefficients j Q) F)
    H≠0 ∧ ∃ d, H.coeff d≠0 ∧ (∀ e<d,H.coeff e=0) ∧
      ∀ (M : Ideal (State q k)) [M.IsMaximal],
        M ∈ (Ideal.span (Set.range (fun i => dehom (Q i)))).minimalPrimes →
          outputTest j (H.coeff d)∈M ∧ ∀c : k,X j-C c∈M → (H.coeff d).IsRoot c := by
  intro H
  have nonzero : H≠0 := by
    intro z
    apply reduced_deformation_ne_zero (inputCoefficients j Q) F divides
    apply Polynomial.Bivariate.swap.injective
    simpa only [map_zero] using z
  have select (n : ℕ) (count : n=Fintype.card (Fin q)) (g : Fin n → Polynomial (State q k))
      (member : H.eval₂ (Polynomial.C.comp (outputTest j)) Polynomial.X∈Ideal.span (Set.range g)) :
      ∃ d,H.coeff d≠0 ∧ (∀ e<d,H.coeff e=0) ∧ ∀ (M : Ideal (State q k)) [M.IsMaximal],
        M ∈ ((Ideal.span (Set.range g)).map (Polynomial.evalRingHom 0)).minimalPrimes →
          outputTest j (H.coeff d)∈M := by
    subst n
    exact StationaryDeformation.common_first_coefficient g (outputTest j) H nonzero member
  obtain ⟨d,nd,before,all⟩ := select q (Fintype.card_fin q).symm (deformedSquare Q)
    (concrete_deformation_membership F rel j Q hom)
  refine ⟨nonzero,d,nd,before,?_⟩
  intro M _ minM
  have inM := all M (by simpa only [square_at_zero] using minM)
  exact ⟨inM,fun c hc => root_of_test_mem M j c hc _ inM⟩


end
end PlanarUnitDistances.UniversalIncidence
