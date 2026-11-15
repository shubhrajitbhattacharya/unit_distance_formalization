import PlanarUnitDistances.RareIntegral
import PlanarUnitDistances.RecordComparison

namespace OAI.PlanarUnitDistances.PhysicalLevels
open Set Finset MeasureTheory FiniteLaw
open scoped Classical
noncomputable section
variable {P Q I : Type*} [Fintype P] [Fintype Q] [Fintype I]

/-- The three summands use the level class of the original incidence law,
even when the score itself is computed conditionally on a list. -/
def levelScore (π : Law (P×Q)) (t : Record P Q) (c g v : ℝ) :=
  if common π t then c else if good π t then g else -v

theorem avg_levelScore (π : Law (P×Q)) (t : Record P Q) (μ : Law I) (c g v : I → ℝ) :
    avg μ (fun i => levelScore π t (c i) (g i) (v i)) =
      levelScore π t (avg μ c) (avg μ g) (avg μ v) := by
  by_cases hc : common π t <;> by_cases hg : good π t <;>
    simp [levelScore,hc,hg,avg,Finset.sum_neg_distrib]

theorem integral_levelScore (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν]
    (c g v : Record P Q → ℝ) :
    (∫ t, levelScore π t (c t) (g t) (v t) ∂ν) =
      (∫ t, c t ∂commonLaw π ν) + rareIntegral π ν g v := by
  let A := {t : Record P Q | common π t}
  let B := goodRare π
  let C := badRare π
  have split (t : Record P Q) : levelScore π t (c t) (g t) (v t) =
      A.indicator c t + (B.indicator g t - C.indicator v t) := by
    by_cases hc : common π t <;> by_cases hg : good π t <;>
      simp [levelScore,A,B,C,goodRare,badRare,Set.indicator,hc,hg]
  simp_rw [split]
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite,
    integral_indicator (Set.toFinite A).measurableSet,
    integral_indicator (Set.toFinite B).measurableSet,
    integral_indicator (Set.toFinite C).measurableSet]
  rfl

end
end OAI.PlanarUnitDistances.PhysicalLevels
