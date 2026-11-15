import Mathlib

namespace PlanarUnitDistances.IntegralFactorHeight

private theorem interpolation_budget_aux (m N d a b c j k : ℕ)
    (hN : N ≤ 2^j) (hs : d+1 ≤ 2^a) (ht : 2*(2*d+2) ≤ 2^b)
    (u : ℕ) (hu : u*(2*d) ≤ 2^c) (last : a*m+(j*N+c*N)+(b*d)*m ≤ k) :
    (d+1)^m * ((N.factorial * (u*(2*d))^N) * ((2*(2*d+2))^d)^m) ≤ 2^k := by
  have hf : N.factorial ≤ (2^j)^N := N.factorial_le_pow.trans (Nat.pow_le_pow_left hN N)
  calc
    _ ≤ (2^a)^m * (((2^j)^N * (2^c)^N) * (((2^b)^d)^m)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hs _) (Nat.mul_le_mul
        (Nat.mul_le_mul hf (Nat.pow_le_pow_left hu _))
        (Nat.pow_le_pow_left (Nat.pow_le_pow_left ht _) _))
    _ = 2^(a*m+(j*N+c*N)+(b*d)*m) := by
      simp only [←pow_mul, ←pow_add, add_assoc]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) last

/-- The coefficient estimate can use degree 2²⁰⁰ for the large determinant. The smaller
    degree of its common factor is needed later, when the parameters are substituted. -/
theorem interpolation_budget (m N : ℕ) (hm : m ≤ 2^110) (hN : N ≤ 2^200) :
    (2^200+1)^m *
      ((N.factorial * ((2^101)*(2*2^200))^N) *
        ((2 * (2*2^200+2))^(2^200))^m) ≤ 2^(2^400) := by
  apply interpolation_budget_aux m N (2^200) 201 203 303 200 (2^400) hN (by decide) (by decide) (2^101) (by decide)
  omega

end PlanarUnitDistances.IntegralFactorHeight
