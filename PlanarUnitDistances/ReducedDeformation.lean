import PlanarUnitDistances.AffineUniversalRelation

namespace PlanarUnitDistances.UniversalIncidence
open HomogeneousMacaulay MvPolynomial
open scoped Matrix
noncomputable section
variable {q : ℕ}

private theorem determinant_on_chart {R : Type*} [CommRing R] (A : Coefficients q R) (x : Coord q → R)
    (hx : x none=1) (root : ∀ i,eval x (form A i)=0) : (matrix A).det=0 := by
  let v (a : Row q) : R := eval x (monomial a.val 1)
  have kill : matrix A *ᵥ v=0 := by
    ext a
    have eq := matrix_evaluation A x a
    rw [root,mul_zero] at eq
    exact eq
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors kill (i:=pureMon none (q+1))
  change eval x (monomial (Finsupp.single none (q+1)) (1 : R))∈_
  rw [←X_pow_eq_monomial,map_pow,eval_X,hx,one_pow]
  exact one_mem _

theorem original_determinant_in_kernel : incidenceMap (universalDeterminant q)=0 := by
  rw [incidenceMap,specialize]
  exact determinant_on_chart _ affinePoint rfl affine_common_zero

def deformationMap {R : Type*} [CommRing R] (A : Coefficients q R) :
    BlockMacaulay.Universal q →+* Polynomial (Polynomial R) :=
  eval₂Hom (Int.castRingHom _) (fun e : Parameter q =>
    deformed (fun i m => Polynomial.C (Polynomial.C (A i m)))
      (Polynomial.C Polynomial.X) Polynomial.X e.1 e.2)

theorem reduced_deformation_ne_zero {R : Type*} [CommRing R] [Nontrivial R] (A : Coefficients q R)
    (F : BlockMacaulay.Universal q) (divides : F ∣ universalDeterminant q) : deformationMap A F≠0 := by
  have div := map_dvd (deformationMap A) divides
  have full : deformationMap A (universalDeterminant q)=eliminationPolynomial A :=
    specialize (deformed (fun i m => Polynomial.C (Polynomial.C (A i m)))
      (Polynomial.C Polynomial.X) Polynomial.X)
  rw [full] at div
  intro zero
  rw [zero,zero_dvd_iff] at div
  exact elimination_nonzero A div

theorem deformation_evaluation {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Coefficients q R) (ε T : S) :
    (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom f ε) T).comp (deformationMap A)=
      eval₂Hom (Int.castRingHom _) (fun e : Parameter q =>
        deformed (fun i m => f (A i m)) ε T e.1 e.2) := by
  apply MvPolynomial.ringHom_ext
  · intro n
    simp [deformationMap]
  · intro e
    simp only [RingHom.comp_apply,deformationMap,eval₂Hom_X',map_deformed]
    simp


end
end PlanarUnitDistances.UniversalIncidence
