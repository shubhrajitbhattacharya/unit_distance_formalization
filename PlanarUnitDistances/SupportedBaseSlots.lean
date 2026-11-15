import PlanarUnitDistances.RecordSlot
import PlanarUnitDistances.PositiveAtoms
import PlanarUnitDistances.GlobalConditionalFlanks

namespace OAI.PlanarUnitDistances.PhysicalLevels
open Finset MeasureTheory FiniteLaw StarScore
open _root_.PlanarUnitDistances.Flanks
open scoped Classical
noncomputable section
variable {P Q I : Type*} [Fintype P] [Fintype Q] [Fintype I]

theorem base_onPositive (π : Law (P×Q)) (μ : Law I) (edge : I → P×Q) (base : P⊕Q)
    (neighbor : I → P⊕Q) (label : Record P Q → Finset (P⊕Q)×Finset (P⊕Q))
    (i j : PositiveAtom μ) (t : Record P Q) :
    baseSlot π (onPositive μ) (fun i => edge i.val) base (fun i => neighbor i.val)
        label i j t = baseSlot π μ edge base neighbor label i.val j.val t := by
  unfold baseSlot
  dsimp only
  rw [onPositive_frequency μ (fun i => t.bit (edge i).1 (edge i).2)]
  rfl

private lemma off_avg_eq (μ : Law I) (f : I×I → ℝ) :
    offAvg μ.val f = avg (pair μ μ) (fun x => if x.1=x.2 then 0 else f x) := by
  unfold offAvg avg
  apply sum_congr rfl
  rintro ⟨i,j⟩ _
  by_cases e : i=j <;> simp [offWeight,pair,e]

/-- The product law loses no off-diagonal contribution when its zero atoms
are removed. Both slots retain their original indices and bias. -/
theorem off_base_onPositive (π : Law (P×Q)) (ν : Measure (Record P Q))
    (μ : Law I) (edge : I → P×Q) (base : P⊕Q) (neighbor : I → P⊕Q)
    (label : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)) :
    offAvg (onPositive μ).val (fun ij => ∫t,baseSlot π (onPositive μ)
        (fun i => edge i.val) base (fun i => neighbor i.val) label ij.1 ij.2 t ∂ν) =
      offAvg μ.val (fun ij => ∫t,baseSlot π μ edge base neighbor label ij.1 ij.2 t ∂ν) := by
  rw [off_avg_eq,off_avg_eq,← onPositive_pair_avg μ μ]
  apply avg_congr
  rintro ⟨i,j⟩
  by_cases e : i=j
  · simp [e]
  · have ev : i.val≠j.val := fun h => e (Subtype.ext h)
    simp only [e,ev,ite_false,base_onPositive]

end
end OAI.PlanarUnitDistances.PhysicalLevels
