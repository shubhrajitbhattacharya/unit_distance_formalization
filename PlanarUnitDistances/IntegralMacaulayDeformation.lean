import PlanarUnitDistances.UniversalFactorCoefficientSum
import PlanarUnitDistances.AffineUniversalRelation

namespace PlanarUnitDistances.MacaulayFactorBounds
open HomogeneousMacaulay BlockMacaulay IntegralFactorHeight EliminantHeight MvPolynomial Finset
open scoped Classical
noncomputable section

abbrev DeformationParameter (q : ℕ) := Option (Option (Parameter q))

/-- The outer variable is T, the inner extra variable is ε. -/
def genericDeformedEntry {q : ℕ} (e : Parameter q) : MvPolynomial (DeformationParameter q) ℤ :=
  deformed (fun i m => X (some (some ⟨i,m⟩))) (X (some none)) (X none) e.1 e.2

private theorem size_X {σ : Type*} (i : σ) : coefficientSum (X i : MvPolynomial σ ℤ) = 1 :=
  coefficientSum_monomial _ 1

private theorem size_neg_X {σ : Type*} (i : σ) : coefficientSum (-X i : MvPolynomial σ ℤ) ≤ 1 := by
  have h := coefficientSum_mul_le (C (-1) : MvPolynomial σ ℤ) (X i)
  rw [coefficientSum_C, size_X] at h
  simpa using h

/-- Each deformed generic coefficient is a single parameter plus at most one signed
    deformation parameter. This verifies the coefficient cost for the actual deformation. -/
theorem generic_entry_size {q : ℕ} (e : Parameter q) : coefficientSum (genericDeformedEntry e) ≤ 2 := by
  obtain ⟨i,m⟩ := e
  unfold genericDeformedEntry deformed
  apply (coefficientSum_add_le ..).trans
  rw [size_X]
  unfold monomialSystem
  split
  · rw [mul_one]
    cases i with
    | none =>
      change 1 + coefficientSum (-X _ : MvPolynomial _ ℤ) ≤ 2
      have h := size_neg_X (σ:=DeformationParameter q) none
      omega
    | some j => simp [size_X]
  · simp [coefficientSum]

theorem generic_entry_degree {q : ℕ} (e : Parameter q) : (genericDeformedEntry e).totalDegree ≤ 1 := by
  obtain ⟨i,m⟩ := e
  unfold genericDeformedEntry deformed
  apply (totalDegree_add ..).trans
  simp only [totalDegree_X, max_le_iff, true_and, le_refl]
  unfold monomialSystem
  split
  · rw [mul_one]
    cases i <;> simp [totalDegree_neg]
  · simp

theorem generic_deformation_degree {q : ℕ} (F : Universal q) :
    (F.eval₂ C genericDeformedEntry).totalDegree ≤ F.totalDegree := by
  rw [eval₂_eq]
  apply totalDegree_finsetSum_le
  intro a ha
  apply (totalDegree_mul ..).trans
  rw [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd ..).trans
  calc
    _ ≤ ∑ i ∈ a.support, a i := sum_le_sum fun i _ => by
      apply (totalDegree_pow ..).trans
      simpa using Nat.mul_le_mul_left (a i) (generic_entry_degree i)
    _ ≤ _ := le_totalDegree ha

private theorem deformation_exponents (d : ℕ) (hd : d < 2^104) : 2^400+d ≤ 2^401 := by omega

theorem generic_deformation_size {q : ℕ} (hq : q ≤ 98) (F : Universal q)
    (hdiv : ∀ i, F ∣ minor i) :
    coefficientSum (F.eval₂ C genericDeformedEntry) ≤ 2^(2^401) := by
  have h := coefficientSum_substitution_le F genericDeformedEntry (by decide : 0 < 2) generic_entry_size
  have d := degree_budget hdiv hq
  apply h.trans
  have aux (L k v t : ℕ) (hL : L ≤ 2^v) (hcap : v+k ≤ t) :
      L*2^k ≤ 2^t := by
    calc
      _ ≤ 2^v * 2^k := Nat.mul_le_mul_right _ hL
      _ = _ := (pow_add 2 v k).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) hcap
  exact aux _ _ (2^400) (2^401) (factor_coefficient_sum hq none F (hdiv none)) (deformation_exponents _ d)

/-- A single integral generator of the actual affine incidence kernel has all four
    degree and coefficient bounds, before and after adjoining ε and T. -/
theorem exists_bounded_incidence_relation (q : ℕ) (hq : q ≤ 98) :
    ∃ F : Universal q, F ≠ 0 ∧ UniversalIncidence.incidenceMap F = 0 ∧
      (∀ G : Universal q, UniversalIncidence.incidenceMap G = 0 ↔ F ∣ G) ∧
      F.totalDegree < 2^104 ∧ coefficientSum F ≤ 2^(2^400) ∧
      (F.eval₂ C genericDeformedEntry).totalDegree < 2^104 ∧
      coefficientSum (F.eval₂ C genericDeformedEntry) ≤ 2^(2^401) := by
  obtain ⟨F, hn, hr, hker, _⟩ := UniversalIncidence.exists_incidence_relation q
  have hd (i : Coord q) : F ∣ minor i := (hker _).mp (UniversalIncidence.minor_in_kernel i)
  have hdeg := degree_budget hd hq
  exact ⟨F, hn, hr, hker, hdeg, factor_coefficient_sum hq none F (hd none),
    (generic_deformation_degree F).trans_lt hdeg, generic_deformation_size hq F hd⟩

end
end PlanarUnitDistances.MacaulayFactorBounds
