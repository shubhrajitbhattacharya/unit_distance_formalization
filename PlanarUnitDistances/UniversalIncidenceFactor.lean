import Mathlib

/-! Once all but one universal coefficient are algebraically independent on
the affine incidence parametrization, its ideal of relations is principal.
Every determinantal relation is divisible by the same polynomial. -/

namespace PlanarUnitDistances.UniversalIncidence
open Polynomial Ideal
open scoped nonZeroDivisors Polynomial
noncomputable section

attribute [local instance] Polynomial.algebra Polynomial.isLocalization in
theorem relation_ideal_principal {R B : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [CommRing B] [IsDomain B]
    (φ : R[X] →+* B) (faithful : Function.Injective (φ.comp C))
    (nonzero : RingHom.ker φ ≠ ⊥) : (RingHom.ker φ).IsPrincipal := by
  let P := RingHom.ker φ
  let K := FractionRing R
  let M := R⁰.map (C : R →+* R[X])
  have disj : Disjoint (M : Set R[X]) (P : Set R[X]) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨a,ha,rfl⟩ hp
    have hzero : (φ.comp C) a = 0 := hp
    exact nonZeroDivisors.ne_zero ha (faithful (hzero.trans (map_zero _).symm))
  have prime : P.IsPrime := RingHom.ker_isPrime φ
  have prime' := IsLocalization.isPrime_of_isPrime_disjoint M K[X] P prime disj
  have h := IsLocalization.height_map_of_disjoint (S := K[X]) M P disj
  have bound := Ideal.height_le_ringKrullDim_of_ne_top prime'.ne_top
  rw [h, IsPrincipalIdealRing.ringKrullDim_eq_one K[X] (Polynomial.not_isField K)] at bound
  have hle : P.height ≤ 1 := by exact_mod_cast bound
  have hne : P.height ≠ 0 := Ideal.height_eq_zero_iff_eq_bot.not.mpr nonzero
  exact UniqueFactorizationMonoid.isPrincipal_of_height_eq_one (le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne))

theorem exists_common_relation {R B : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [CommRing B] [IsDomain B]
    (φ : R[X] →+* B) (faithful : Function.Injective (φ.comp C))
    (w : R[X]) (hw : w ≠ 0) (vanishes : φ w = 0) :
    ∃ p : R[X], p ≠ 0 ∧ φ p = 0 ∧ ∀ g, φ g = 0 ↔ p ∣ g := by
  have hn : RingHom.ker φ ≠ ⊥ := fun h => hw (by
    have hw' : w ∈ RingHom.ker φ := vanishes
    simpa [h] using hw')
  obtain ⟨p,hp⟩ := relation_ideal_principal φ faithful hn
  have mem (g : R[X]) : φ g = 0 ↔ p ∣ g := by
    change g ∈ RingHom.ker φ ↔ _
    rw [hp, Ideal.mem_span_singleton]
  exact ⟨p,fun hz => hn (by simp [hp,hz]), (mem p).mpr dvd_rfl, mem⟩

end
end PlanarUnitDistances.UniversalIncidence
