import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.RingTheory.Localization.FractionRing

namespace PlanarUnitDistances.UniversalIncidence
open MvPolynomial Finset
noncomputable section
variable {k S : Type*} [Field k]

def parameterCoefficient (P : Polynomial (MvPolynomial S k)) (m : S →₀ ℕ) : Polynomial k :=
  ∑ n ∈ P.support,Polynomial.monomial n ((P.coeff n).coeff m)

@[simp] theorem parameterCoefficient_coeff (P : Polynomial (MvPolynomial S k)) (m : S →₀ ℕ) (n : ℕ) :
    (parameterCoefficient P m).coeff n=(P.coeff n).coeff m := by
  classical
  rw [parameterCoefficient,Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial,Finset.sum_ite_eq',ite_eq_left_iff]
  intro hn
  simp [Polynomial.notMem_support_iff.mp hn]

theorem parameterCoefficient_evaluation (P : Polynomial (MvPolynomial S k)) (m : S →₀ ℕ) (c : k) :
    (parameterCoefficient P m).eval c=(P.eval (C c)).coeff m := by
  rw [parameterCoefficient,Polynomial.eval_finsetSum,Polynomial.eval_eq_sum (p:=P),Polynomial.sum_def,coeff_sum]
  apply sum_congr rfl
  intro n _
  rw [Polynomial.eval_monomial,←map_pow,mul_comm (P.coeff n),coeff_C_mul,mul_comm]

/-- A single monomial in the independent slicing parameters yields a
nonzero base-field polynomial vanishing on every base-field coordinate
annihilated by the original equation over the rational-function field. -/
theorem extract_base_field_polynomial (P : Polynomial (MvPolynomial S k)) (nonzero : P≠0)
    {L : Type*} [CommRing L] (inclusion : MvPolynomial S k →+* L) (injective : Function.Injective inclusion) :
    ∃ m, parameterCoefficient P m≠0 ∧ ∀ c : k,
      (P.map inclusion).IsRoot (inclusion (C c)) → (parameterCoefficient P m).IsRoot c := by
  have some_n : ∃ n,P.coeff n≠0 := by
    by_contra! h
    exact nonzero (Polynomial.ext (by simpa using h))
  obtain ⟨n,hn⟩ := some_n
  obtain ⟨m,hm⟩ := MvPolynomial.exists_coeff_ne_zero hn
  have selected : parameterCoefficient P m≠0 := by
    intro zero
    apply hm
    rw [←parameterCoefficient_coeff P m n,zero,Polynomial.coeff_zero]
  refine ⟨m,selected,?_⟩
  intro c root
  have ev : P.eval (C c)=0 := injective (by
    rw [inclusion.map_zero,←Polynomial.eval₂_hom inclusion,←Polynomial.eval_map]
    exact root)
  change (parameterCoefficient P m).eval c=0
  simp [parameterCoefficient_evaluation,ev]

end
end PlanarUnitDistances.UniversalIncidence
