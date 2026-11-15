import PlanarUnitDistances.IntegralSpecializationHeight
import Mathlib.Data.Finsupp.Option

namespace PlanarUnitDistances.EliminantHeight
open MvPolynomial Finset
open scoped Classical
noncomputable section
variable {A : Type*}

/-- Attach the homogenizing exponent. Restricting the exponent vector
to its original coordinates gives a left inverse. -/
private def completeExponent (D : ℕ) : (A →₀ ℕ) ↪ (Option A →₀ ℕ) where
  toFun m := m.optionElim (D-m.degree)
  inj' m n h := by simpa only [Finsupp.some_optionElim] using congrArg Finsupp.some h

/-- Homogenize an integral coefficient polynomial while retaining its
coefficient vector, indexed by the lifted exponent vectors. -/
def homogeneousCoefficient (D : ℕ) (p : MvPolynomial A ℤ) : MvPolynomial (Option A) ℤ :=
  AddMonoidAlgebra.ofCoeff ((AddMonoidAlgebra.coeff p).embDomain (completeExponent D))

private theorem completedSupport (D : ℕ) (p : MvPolynomial A ℤ) :
    (homogeneousCoefficient D p).support=p.support.map (completeExponent D) :=
  Finsupp.support_embDomain _ _

private theorem completedCoeff (D : ℕ) (p : MvPolynomial A ℤ) (m : A →₀ ℕ) :
    (homogeneousCoefficient D p).coeff (completeExponent D m)=p.coeff m :=
  Finsupp.embDomain_apply_self _ _ _

theorem homogeneousCoefficient_size (D : ℕ) (p : MvPolynomial A ℤ) :
    coefficientSum (homogeneousCoefficient D p)=coefficientSum p := by
  simp [coefficientSum,completedSupport,Finset.sum_map,completedCoeff]

theorem homogeneousCoefficient_degree [Fintype A] {D : ℕ} (p : MvPolynomial A ℤ)
    (h : p.totalDegree≤D) : (homogeneousCoefficient D p).IsHomogeneous D := by
  intro m hm
  have mem := mem_support_iff.mpr hm
  rw [completedSupport,mem_map] at mem
  obtain ⟨u,hu,rfl⟩ := mem
  have le : u.degree ≤ D := (MvPolynomial.le_totalDegree hu).trans h
  change Finsupp.weight (fun _ : Option A => (1 : ℕ)) ((completeExponent D) u)=D
  rw [←Finsupp.degree_eq_weight_one,Finsupp.degree_eq_sum,Fintype.sum_option]
  change u.optionElim (D-u.degree) none + ∑ i, u.optionElim (D-u.degree) (some i)=D
  simp only [Finsupp.optionElim_apply_none,Finsupp.optionElim_apply_some,←Finsupp.degree_eq_sum]
  omega

theorem homogeneousCoefficient_aeval [Fintype A] {K : Type*} [Field K] (D : ℕ)
    (p : MvPolynomial A ℤ) (a : A → K) :
    aeval (fun j : Option A => j.elim 1 a) (homogeneousCoefficient D p)=aeval a p := by
  change MvPolynomial.eval₂ (Int.castRingHom K) _ _ = MvPolynomial.eval₂ (Int.castRingHom K) _ _
  simp only [eval₂_eq',completedSupport,Finset.sum_map,completedCoeff]
  apply sum_congr rfl
  intro d _
  have atSome (i : A) : completeExponent D d (some i)=d i := Finsupp.optionElim_apply_some _ _ _
  rw [Fintype.prod_option]
  simp only [Option.elim_none,Option.elim_some,one_pow,one_mul,atSome]

end
end PlanarUnitDistances.EliminantHeight
