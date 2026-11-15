import PlanarUnitDistances.IntegralSpecializationHeight
import Mathlib

namespace PlanarUnitDistances.EliminantHeight
open MvPolynomial Finset
noncomputable section

variable {σ τ : Type*}

private theorem sum_restrict_coeff (f : MvPolynomial σ ℤ) (S : Finset (σ →₀ ℕ)) :
    (∑ a ∈ S, (f.coeff a).natAbs) ≤ coefficientSum f := by
  classical
  let U := S ∪ f.support
  have hS : S ⊆ U := subset_union_left
  have hf : f.support ⊆ U := subset_union_right
  have hU : coefficientSum f = ∑ a ∈ U, (f.coeff a).natAbs := by
    refine sum_subset hf (fun a _ ha => ?_)
    simp [notMem_support_iff.mp ha]
  rw [hU]
  exact sum_le_sum_of_subset_of_nonneg hS (by intros; omega)

theorem coefficientSum_add_le (f g : MvPolynomial σ ℤ) :
    coefficientSum (f+g) ≤ coefficientSum f + coefficientSum g := by
  unfold coefficientSum
  simp only [AddMonoidAlgebra.coeff_add]
  calc
    _ ≤ ∑ a ∈ (f+g).support, ((f.coeff a).natAbs + (g.coeff a).natAbs) :=
      sum_le_sum fun _ _ => Int.natAbs_add_le _ _
    _ ≤ _ := by rw [sum_add_distrib]; exact Nat.add_le_add (sum_restrict_coeff ..) (sum_restrict_coeff ..)

theorem coefficientSum_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    coefficientSum (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coefficientSum (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coefficientSum]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (coefficientSum_add_le ..).trans (Nat.add_le_add_left ih _)

@[simp] theorem coefficientSum_monomial (d : σ →₀ ℕ) (c : ℤ) :
    coefficientSum (monomial d c) = c.natAbs := by
  classical
  by_cases hc : c = 0
  · simp [coefficientSum, hc]
  · simp [coefficientSum, support_monomial, hc, coeff_monomial]

@[simp] theorem coefficientSum_C (c : ℤ) : coefficientSum (C c : MvPolynomial σ ℤ) = c.natAbs := by
  exact coefficientSum_monomial 0 c

@[simp] theorem coefficientSum_one : coefficientSum (1 : MvPolynomial σ ℤ) = 1 := by
  simpa only [map_one, Int.natAbs_one] using (coefficientSum_C (σ := σ) 1)

theorem coefficientSum_mul_le (f g : MvPolynomial σ ℤ) :
    coefficientSum (f*g) ≤ coefficientSum f * coefficientSum g := by
  classical
  have he : f*g = ∑ a ∈ f.support, ∑ b ∈ g.support,
      monomial (a+b) (f.coeff a * g.coeff b) := by
    conv_lhs => rw [f.as_sum, g.as_sum]
    simp only [sum_mul, mul_sum, monomial_mul_monomial]
    rw [sum_comm]
  rw [he]
  exact (coefficientSum_sum_le ..).trans <| (sum_le_sum fun _ _ => coefficientSum_sum_le ..).trans <| by
    simp only [coefficientSum_monomial, Int.natAbs_mul, ← mul_sum, ← sum_mul]
    exact le_refl _

theorem coefficientSum_pow_le (f : MvPolynomial σ ℤ) (k : ℕ) :
    coefficientSum (f^k) ≤ (coefficientSum f)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ]
    exact (coefficientSum_mul_le ..).trans (Nat.mul_le_mul_right _ ih)

theorem coefficientSum_prod_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    coefficientSum (∏ i ∈ s, f i) ≤ ∏ i ∈ s, coefficientSum (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (coefficientSum_mul_le ..).trans (Nat.mul_le_mul_left _ ih)

/-- Integral polynomial substitution costs one factor of the largest coefficient sum per
    degree. The estimate applies with arbitrarily many target parameters. -/
theorem coefficientSum_substitution_le (f : MvPolynomial σ ℤ) (b : σ → MvPolynomial τ ℤ)
    {M : ℕ} (hM : 0 < M) (hb : ∀ i, coefficientSum (b i) ≤ M) :
    coefficientSum (f.eval₂ C b) ≤ coefficientSum f * M ^ f.totalDegree := by
  classical
  rw [eval₂_eq]
  apply (coefficientSum_sum_le ..).trans
  rw [coefficientSum, sum_mul]
  apply sum_le_sum
  intro a ha
  apply (coefficientSum_mul_le ..).trans
  rw [coefficientSum_C]
  apply Nat.mul_le_mul_left
  apply (coefficientSum_prod_le ..).trans
  calc
    _ ≤ ∏ i ∈ a.support, M^(a i) := prod_le_prod (fun i _ =>
      (coefficientSum_pow_le ..).trans (Nat.pow_le_pow_left (hb i) _))
    _ = M ^ (a.sum fun _ e => e) := prod_pow_eq_pow_sum a.support (fun i => a i) M
    _ ≤ M ^ f.totalDegree := Nat.pow_le_pow_right hM (le_totalDegree ha)


end
end PlanarUnitDistances.EliminantHeight
