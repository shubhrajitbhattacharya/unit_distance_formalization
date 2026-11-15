import Mathlib

/-! Integer interpolation using division by a monic linear polynomial. -/
namespace PlanarUnitDistances.IntegralFactorHeight

open Polynomial

/-- Values at any sufficiently large set of distinct integer nodes control every coefficient.
    The estimate allows holes in the set of nodes and includes constant polynomials. -/
theorem coeff_le_of_integer_nodes (d : ℕ) (p : ℤ[X]) (S : Finset ℤ) (M B : ℕ)
    (hd : p.natDegree ≤ d) (hcard : d < S.card)
    (hsize : ∀ x ∈ S, Int.natAbs x ≤ M)
    (hval : ∀ x ∈ S, (p.eval x).natAbs ≤ B) (k : ℕ) :
    (p.coeff k).natAbs ≤ B * (2 * (M + 2)) ^ d := by
  induction d generalizing p S B k with
  | zero =>
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hcard
    have hp := eq_C_of_natDegree_le_zero hd
    have hv := hval x hx
    rw [hp, eval_C] at hv
    rw [hp, coeff_C]
    split
    · simpa only [pow_zero, mul_one] using hv
    · simp
  | succ d ih =>
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    let q := p /ₘ (X - C x)
    have hrec : C (p.eval x) + (X - C x) * q = p := by
      rw [← modByMonic_X_sub_C_eq_C_eval p x]
      exact p.modByMonic_add_div (X - C x)
    have hqd : q.natDegree ≤ d := by
      rw [show q = p /ₘ (X - C x) from rfl, natDegree_divByMonic _ (monic_X_sub_C x),
        natDegree_X_sub_C]
      omega
    have hsmall : ∀ i, (q.coeff i).natAbs ≤ (2 * B) * (2 * (M + 2)) ^ d := by
      intro i
      refine ih q (S.erase x) (2 * B) hqd ?_ ?_ ?_ i
      · rw [Finset.card_erase_of_mem hx]
        omega
      · exact fun _ ht => hsize _ (Finset.mem_erase.mp ht).2
      · intro t ht
        obtain ⟨htx, htS⟩ := Finset.mem_erase.mp ht
        have he := congrArg (eval t) hrec
        simp only [eval_add, eval_C, eval_mul, eval_sub, eval_X] at he
        have hs : (t - x) * q.eval t = p.eval t - p.eval x := by omega
        have hdiff : 1 ≤ (t - x).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr htx)
        calc
          (q.eval t).natAbs ≤ (t - x).natAbs * (q.eval t).natAbs :=
            Nat.le_mul_of_pos_left _ hdiff
          _ = (p.eval t - p.eval x).natAbs := by rw [← Int.natAbs_mul, hs]
          _ ≤ (p.eval t).natAbs + (p.eval x).natAbs := Int.natAbs_sub_le _ _
          _ ≤ 2 * B := by have := hval t htS; have := hval x hx; omega
    have hpos : 1 ≤ (2 * (M + 2)) ^ d := Nat.pow_pos (by omega)
    have hxB := hval x hx
    have hxM := hsize x hx
    have hm (i : ℕ) : (x * q.coeff i).natAbs ≤ M * ((2 * B) * (2 * (M + 2)) ^ d) := by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul hxM (hsmall i)
    rw [← hrec, coeff_add, pow_succ]
    cases k with
    | zero =>
      simp only [coeff_C_zero, sub_mul, coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub]
      calc
        _ ≤ (p.eval x).natAbs + (-(x * q.coeff 0)).natAbs := Int.natAbs_add_le _ _
        _ ≤ B + M * ((2 * B) * (2 * (M + 2)) ^ d) := by
          simpa only [Int.natAbs_neg] using Nat.add_le_add hxB (hm 0)
        _ ≤ _ := by nlinarith [Nat.mul_le_mul_left B hpos]
    | succ k =>
      simp only [coeff_C_succ, zero_add, coeff_X_sub_C_mul]
      calc
        _ ≤ (q.coeff k).natAbs + (x * q.coeff (k + 1)).natAbs := Int.natAbs_sub_le _ _
        _ ≤ (2 * B) * (2 * (M + 2)) ^ d + M * ((2 * B) * (2 * (M + 2)) ^ d) :=
          Nat.add_le_add (hsmall k) (hm (k + 1))
        _ ≤ _ := by nlinarith

end PlanarUnitDistances.IntegralFactorHeight
