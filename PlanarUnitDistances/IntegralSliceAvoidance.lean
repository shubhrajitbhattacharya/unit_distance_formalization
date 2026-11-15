import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Order.Filter.Finite

namespace PlanarUnitDistances.StationaryDeformation
open Polynomial Filter Finset
noncomputable section

/-- For all but finitely many natural numbers, this integral combination
avoids every prime in a fixed finite list that misses at least one equation. -/
theorem cofinite_prime_avoidance {k R : Type*} [Field k] [CharZero k] [CommRing R]
    [Algebra k R] {m : ℕ} (g : Fin m → R) (primes : Finset (Ideal R))
    (hp : ∀ p ∈ primes, p.IsPrime) (misses : ∀ p ∈ primes, ∃ j, g j ∉ p) :
    ∀ᶠ a : ℕ in cofinite, ∀ p ∈ primes, (∑ i : Fin m, (a : R)^(i:ℕ)*g i) ∉ p := by
  classical
  apply (eventually_all_finset primes).mpr
  intro p hmem
  let := hp p hmem
  let : CharZero (R ⧸ p) := Algebra.charZero_of_charZero k _
  let H : Polynomial (R ⧸ p) := ∑ i : Fin m, monomial (i:ℕ) ((Ideal.Quotient.mk p) (g i))
  obtain ⟨j, hj⟩ := misses p hmem
  have coeff : H.coeff j = Ideal.Quotient.mk p (g j) := by
    dsimp [H]
    rw [finsetSum_coeff, Finset.sum_eq_single j]
    · simp
    · intro i _ different
      simp only [coeff_monomial]
      split_ifs with h
      · exact False.elim (different (Fin.ext (by first | exact h | exact h.symm)))
      · rfl
    · simp
  have nonzero : H ≠ 0 := fun h => hj <| Ideal.Quotient.eq_zero_iff_mem.mp <| by
    rw [← coeff, h, coeff_zero]
  have eventuallyGood := (Nat.cast_injective (R := R ⧸ p)).tendsto_cofinite.eventually
    (Polynomial.eventually_eval_ne_zero_cofinite nonzero)
  filter_upwards [eventuallyGood] with a ha
  intro bad
  apply ha
  have eq := Ideal.Quotient.eq_zero_iff_mem.mpr bad
  simpa [H, Polynomial.eval_finsetSum, mul_comm] using eq

end
end PlanarUnitDistances.StationaryDeformation
