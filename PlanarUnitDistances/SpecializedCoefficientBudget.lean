import PlanarUnitDistances.DeformationCoefficientHeight
import PlanarUnitDistances.IntegralSubstitutionDegree

namespace PlanarUnitDistances.MacaulayFactorBounds
open HomogeneousMacaulay BlockMacaulay EliminantHeight MvPolynomial
noncomputable section

private theorem size_budget (L d p t k : ℕ) (hL : L ≤ 2^p) (h : p+t*d ≤ k) :
    L*(2^t)^d ≤ 2^k := by
  calc
    _ ≤ 2^p*(2^t)^d := Nat.mul_le_mul_right _ hL
    _ = 2^(p+t*d) := by rw [←pow_mul, ←pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) h

private theorem exponents (d : ℕ) (hd : d < 2^104) :
    d*256 ≤ 2^112 ∧ 2^401+200*d ≤ 2^402 := by constructor <;> omega

/-- For any integral table substituted into the q selected quadrics and the test form,
    bound an arbitrary ε- and T-coefficient of the actual swapped nested relation. -/
theorem specialized_coefficient_budget {q : ℕ} (hq : q ≤ 98) (F : Universal q)
    (divides : ∀ i, F ∣ minor i) {σ : Type*} (A : Coefficients q (MvPolynomial σ ℤ))
    (degreeA : ∀ i m, (A i m).totalDegree ≤ 256)
    (sizeA : ∀ i m, coefficientSum (A i m) ≤ 2^200) (j k : ℕ) :
    let P := ((Polynomial.Bivariate.swap (UniversalIncidence.deformationMap A F)).coeff k).coeff j
    P.totalDegree ≤ 2^112 ∧ coefficientSum P ≤ 2^(2^402) := by
  dsimp only
  obtain ⟨G,dG,sG,representation⟩ := specialized_swapped_coefficient hq F divides j k
  rw [representation A]
  have mapC : Int.castRingHom (MvPolynomial σ ℤ) = C := by ext; simp
  rw [mapC]
  let b := fun e : Parameter q => A e.1 e.2
  change (G.eval₂ C b).totalDegree ≤ _ ∧ coefficientSum (G.eval₂ C b) ≤ _
  obtain ⟨d,t⟩ := exponents _ dG
  refine ⟨(totalDegree_substitution_le G b 256 (fun i => degreeA _ _)).trans d, ?_⟩
  exact (coefficientSum_substitution_le G b (Nat.pow_pos (by decide)) (fun i => sizeA _ _)).trans
    (size_budget _ _ (2^401) 200 (2^402) sG t)

end
end PlanarUnitDistances.MacaulayFactorBounds

