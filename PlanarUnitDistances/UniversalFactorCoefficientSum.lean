import PlanarUnitDistances.MacaulayFactorBounds
import PlanarUnitDistances.IntegralFactorHeight
import PlanarUnitDistances.FactorSizeBudget
import PlanarUnitDistances.IntegralSubstitutionSize

namespace PlanarUnitDistances.MacaulayFactorBounds
open HomogeneousMacaulay BlockMacaulay IntegralFactorHeight EliminantHeight MvPolynomial
open scoped Classical
noncomputable section

/-- A bound for every integral factor of one actual Macaulay minor, including constants.
    This applies in particular to the primitive factor shared by all the minors. -/
theorem factor_coefficient_sum {q : ℕ} (hq : q ≤ 98) (i : Coord q)
    (F : Universal q) (hdiv : F ∣ minor i) : coefficientSum F ≤ 2^(2^400) := by
  let N := Fintype.card (Row q)
  have hd : (minor i).totalDegree ≤ 2^200 := (minor_totalDegree i).trans (rows_le q hq)
  have box (u : Parameter q → ℤ) (hu : ∀ e, 0 ≤ u e ∧ u e ≤ (2*2^200 : ℕ)) :
      (eval u (minor i)).natAbs ≤ N.factorial * ((2^101)*(2*2^200))^N := by
    apply minor_box_bound i hq
    intro e
    exact_mod_cast (Int.natAbs_of_nonneg (hu e).1 ▸ (hu e).2 :
      ((u e).natAbs : ℤ) ≤ (2*2^200 : ℕ))
  exact (factor_sum_le _ _ _ F hdiv (minor_ne_zero i) hd box).trans
    (interpolation_budget _ _ (parameter_count_le hq) (rows_le q hq))

end
end PlanarUnitDistances.MacaulayFactorBounds
