import PlanarUnitDistances.PolynomialCoordinateSlice

namespace PlanarUnitDistances.CoordinateSlice
open MvPolynomial Finset
noncomputable section
variable {k V : Type*} [Field k]

/-- Freezing coordinates at independent rational functions does not increase
the degree of any defining equation in the remaining variables. -/
theorem specialize_totalDegree (S : Set V) (p : Poly k V) :
    (specialize k S p).totalDegree ≤ p.totalDegree := by
  classical
  have hx (i : V) : (specialize k S (X i)).totalDegree ≤ 1 := by
    by_cases h : i ∈ S
    · rw [specialize_X_mem (k:=k) S (⟨i,h⟩ : S), totalDegree_C]
      exact Nat.zero_le 1
    · rw [specialize_X_compl (k:=k) S (⟨i,h⟩ : (↑Sᶜ)),totalDegree_X]
  conv_lhs => rw [p.as_sum,map_sum]
  apply totalDegree_finsetSum_le
  intro a ha
  simp only [monomial_eq,Finsupp.prod,map_mul,map_prod,map_pow,specialize_C]
  refine (totalDegree_mul ..).trans ?_
  simp only [totalDegree_C,zero_add]
  refine (totalDegree_finsetProd ..).trans ((sum_le_sum ?_).trans (le_totalDegree ha))
  intro i _
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (a i) (hx i))

end
end PlanarUnitDistances.CoordinateSlice
