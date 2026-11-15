import Mathlib

namespace PlanarUnitDistances.GenericParameters
open Set

/-- A list of k parameters cannot make all k+1 independent coordinates
algebraic, even after passing to its relative algebraic closure. -/
theorem survives_adjoining {F K : Type*} [Field F] [Field K] [Algebra F K]
    {k n : ℕ} (hkn : k < n) (x : Fin n → K) (y : Fin k → K)
    (hx : AlgebraicIndependent F x) :
    ∃ i, Transcendental (algebraicClosure (IntermediateField.adjoin F (range y)) K) (x i) := by
  classical
  let M := AlgebraicIndependent.matroid F K
  have ind : M.Indep (range x) := AlgebraicIndependent.matroid_indep_iff.mpr hx.to_subtype_range
  have small : (range y).encard ≤ k := by
    simpa using Set.encard_image_le y (univ : Set (Fin k))
  have large : (n : ℕ∞) ≤ (range x).encard := by simpa using hx.injective.encard_range.ge
  suffices ∃ i, Transcendental (IntermediateField.adjoin F (range y)) (x i) by
    obtain ⟨i,hi⟩ := this
    exact ⟨i, hi.extendScalars _⟩
  by_contra! halg
  have sub : range x ⊆ M.closure (range y) := by
    rw [show M.closure (range y) = _ from AlgebraicIndependent.matroid_closure_eq]
    rintro _ ⟨i,rfl⟩
    change IsAlgebraic (Algebra.adjoin F (range y)) (x i)
    exact IntermediateField.isAlgebraic_adjoin_iff.mp (not_not.mp (halg i))
  have := (M.eRk_mono sub).trans_eq (M.eRk_closure_eq (range y))
  rw [ind.eRk_eq_encard] at this
  have hle := large.trans (this.trans ((M.eRk_le_encard _).trans small))
  exact (not_le_of_gt hkn) (by exact_mod_cast hle)

/-- Manuscript's eight point abscissas after seven normalized anchor parameters. -/
theorem eight_against_seven {F K : Type*} [Field F] [Field K] [Algebra F K]
    (x : Fin 8 → K) (y : Fin 7 → K) (hx : AlgebraicIndependent F x) :
    ∃ i, Transcendental (algebraicClosure (IntermediateField.adjoin F (range y)) K) (x i) :=
  survives_adjoining (by decide) x y hx

end PlanarUnitDistances.GenericParameters
