import PlanarUnitDistances.IntegralSubstitutionSize

namespace PlanarUnitDistances.EliminantHeight
open MvPolynomial Finset

/-- Total degree under substitution over a commutative semiring, allowing zero or
    constant input polynomials, with a uniform bound D on each substitution entry. -/
theorem totalDegree_substitution_le {R σ τ : Type*} [CommSemiring R]
    (f : MvPolynomial σ R) (b : σ → MvPolynomial τ R) (D : ℕ)
    (hb : ∀ i, (b i).totalDegree ≤ D) :
    (f.eval₂ C b).totalDegree ≤ f.totalDegree * D := by
  classical
  rw [eval₂_eq]
  apply totalDegree_finsetSum_le
  intro a ha
  apply (totalDegree_mul ..).trans
  rw [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd ..).trans
  calc
    _ ≤ ∑ i ∈ a.support, a i * D := sum_le_sum fun i _ =>
      (totalDegree_pow ..).trans (Nat.mul_le_mul_left _ (hb i))
    _ ≤ _ := by rw [←sum_mul]; exact Nat.mul_le_mul_right D (le_totalDegree ha)

end PlanarUnitDistances.EliminantHeight
