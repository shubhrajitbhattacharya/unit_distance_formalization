import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.Data.Set.Card

namespace PlanarUnitDistances.StationaryDeformation
open Polynomial

/-- A minimal component in the special fiber lifts through the parameter whenever
its inverse image has greater height than every minimal prime of the family. -/
theorem exists_horizontal_prime {R S : Type*} [CommRing R] [CommRing S]
    (π : R →+* S) (surj : Function.Surjective π) (t : R)
    (ker_eq : RingHom.ker π = Ideal.span {t}) (I : Ideal R) (P : Ideal S)
    (special : P ∈ (I.map π).minimalPrimes)
    (dim : ∀ Q ∈ I.minimalPrimes, Q.height < (P.comap π).height) :
    ∃ Q ∈ I.minimalPrimes, Q ≤ P.comap π ∧ t ∉ Q := by
  let := special.isPrime
  obtain ⟨Q, hQ, below⟩ := Ideal.exists_minimalPrimes_le (Ideal.map_le_iff_le_comap.mp special.le)
  refine ⟨Q, hQ, below, ?_⟩
  intro ht
  have kernel : RingHom.ker π ≤ Q := by simpa [ker_eq, Ideal.span_singleton_le_iff_mem] using ht
  let := hQ.isPrime
  have prime := Ideal.map_isPrime_of_surjective surj kernel
  have back : (Q.map π).comap π = Q :=
    (Ideal.comap_map_of_surjective π surj Q).trans (sup_eq_left.mpr kernel)
  have eqQ : Q.map π = P :=
    le_antisymm (Ideal.map_le_iff_le_comap.mpr below)
      (special.2 ⟨prime, Ideal.map_mono hQ.le⟩ (Ideal.map_le_iff_le_comap.mpr below))
  exact (dim Q hQ).ne (congrArg Ideal.height (back.symm.trans (congrArg (Ideal.comap π) eqQ)))

/-- For a square system, an isolated point of height at least n in the special
fiber lies on a horizontal component. No Jacobian condition is required. -/
theorem isolated_square_lifts {S : Type*} [CommRing S] [IsNoetherianRing S]
    (n : ℕ) (g : Fin n → Polynomial S) (P : Ideal S) [P.IsMaximal]
    (special : P ∈ ((Ideal.span (Set.range g)).map (evalRingHom 0)).minimalPrimes)
    (height : (n : ℕ∞) ≤ P.height) :
    ∃ Q ∈ (Ideal.span (Set.range g)).minimalPrimes,
      Q ≤ P.comap (evalRingHom 0) ∧ X ∉ Q := by
  let π : Polynomial S →+* S := evalRingHom 0
  have surj : Function.Surjective π := eval_surjective 0
  let M := P.comap π
  let : M.IsMaximal := Ideal.comap_isMaximal_of_surjective π surj
  let : M.LiesOver P := ⟨by ext a; simp [M, π, Ideal.under, Ideal.mem_comap]⟩
  apply exists_horizontal_prime π surj X (by simp [π, ker_evalRingHom]) _ P special
  intro Q hQ
  have hn : (Set.range g).encard ≤ n := by
    simpa using Set.encard_image_le g Set.univ
  have hlt : (n : ℕ∞) < n + 1 := by exact_mod_cast Nat.lt_succ_self n
  exact (Ideal.height_le_encard_of_mem_minimalPrimes_span hQ).trans hn |>.trans_lt
    (hlt.trans_le ((add_le_add height (le_refl (1 : ℕ∞))).trans_eq (Polynomial.height_eq_height_add_one P M).symm))


end PlanarUnitDistances.StationaryDeformation
