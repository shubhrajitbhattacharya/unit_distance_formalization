import PlanarUnitDistances.RareMassBound
import PlanarUnitDistances.RecordComparison

namespace OAI.PlanarUnitDistances.PhysicalLevels
open MeasureTheory FiniteLaw FiniteStarCoupling RareScore CommonTemplate
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

/-- Each endpoint exceptional width has small mean for every rule
obeying local dominance, on the same record measure and good rare set. -/
theorem width_means_of_dominance (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν]
    (l : Record P Q → Finset (P⊕Q) × Finset (P⊕Q))
    (hm : (∫t,inconsistency π t.bit t.x t.y ∂ν) ≤ 4) (hs : 4 ≤ scale π ν)
    (dom : ∀t∈goodRare π,pointException π (rareBit π t) (l t) t.x+
      centerException π (rareBit π t) (l t) t.y ≤ 2*(minority π t+inconsistency π t.bit t.x t.y)) :
    pointWidth π ν (rareBit π) l ≤ 4*scale π ν ∧
      centerWidth π ν (rareBit π) l ≤ 4*scale π ν := by
  let A := goodRare π
  let X (t : Record P Q) := pointException π (rareBit π t) (l t) t.x
  let Y (t : Record P Q) := centerException π (rareBit π t) (l t) t.y
  let m (t : Record P Q) := inconsistency π t.bit t.x t.y
  have raw := setIntegral_mono_on (μ:=ν) (f:=fun t => X t+Y t) (g:=fun t => 2*(minority π t+m t))
    Integrable.of_finite Integrable.of_finite (Set.toFinite A).measurableSet dom
  rw [integral_const_mul,integral_add (f:=minority π) (g:=m) Integrable.of_finite Integrable.of_finite,
    integral_add (f:=X) (g:=Y) Integrable.of_finite Integrable.of_finite] at raw
  have small : (∫t in A,minority π t ∂ν) ≤ scale π ν :=
    integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall
      (fun _ => le_min (event_nonneg ..) (sub_nonneg.mpr (event_le_one ..)))) Integrable.of_finite
  have inc : (∫t in A,m t ∂ν) ≤ (∫t,m t ∂ν) :=
    integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall (fun _ => event_nonneg ..))
      Integrable.of_finite
  have nx : 0≤∫t in A,X t ∂ν := integral_nonneg (fun _ => event_nonneg ..)
  have ny : 0≤∫t in A,Y t ∂ν := integral_nonneg (fun _ => event_nonneg ..)
  change (∫t,m t ∂ν) ≤ 4 at hm
  rw [←pointWidth_integral,←centerWidth_integral]
  change (∫t in A,X t ∂ν) ≤ _ ∧ (∫t in A,Y t ∂ν) ≤ _
  constructor <;> linarith only [raw,small,inc,hm,hs,nx,ny]

end
end OAI.PlanarUnitDistances.PhysicalLevels
