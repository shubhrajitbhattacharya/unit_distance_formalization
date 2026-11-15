import PlanarUnitDistances.RecordSlot
import PlanarUnitDistances.GlobalConditionalFlanks

namespace OAI.PlanarUnitDistances.PhysicalLevels
open MeasureTheory FiniteLaw CommonTemplate RareScore
open _root_.PlanarUnitDistances.Flanks
open scoped Classical
noncomputable section
variable {P Q I : Type*} [Fintype P] [Fintype Q] [Fintype I]

/-- The exceptional width of one tagged vertex under the same record
measure and label assignment as the observed slot. -/
def baseExceptionWidth (π : Law (P×Q)) (ν : Measure (Record P Q))
    (label : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)) (base : P⊕Q) :=
  width ν (fun t => ¬common π t ∧ good π t ∧ exceptional (rareBit π t) (label t) (vertexState t base))

/-- A genuinely coincident pair on this base contributes at most twice
the common width plus twice the exceptional width of that base. -/
theorem base_diagonal_upper (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν]
    (μ : Law I) (edge : I → P×Q) (base : P⊕Q) (neighbor : I → P⊕Q)
    (label : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)) (i : I) :
    (∫t,baseSlot π μ edge base neighbor label i i t ∂ν)≤
      2*(width ν (common π)+baseExceptionWidth π ν label base) := by
  have b (t : Record P Q) : baseSlot π μ edge base neighbor label i i t ≤
      2*ind (common π t)+2*ind (¬common π t ∧ good π t ∧
        exceptional (rareBit π t) (label t) (vertexState t base)) :=
    diagonal_observedSlot _ _ _ _ _ _ _ _ _
  have int := integral_mono (μ:=ν) Integrable.of_finite Integrable.of_finite b
  simp only [integral_add Integrable.of_finite Integrable.of_finite,integral_const_mul] at int
  unfold baseExceptionWidth width
  linarith only [int]

/-- Every ordered iid pair belongs to exactly one of these two sums.
Together with the integrated diagonal estimate this leaves the collision
probability of the actual conditional law as the only diagonal factor. -/
theorem base_all_upper (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν]
    (μ : Law I) (edge : I → P×Q) (base : P⊕Q) (neighbor : I → P⊕Q)
    (label : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)) :
    let score := fun p : I×I => ∫t,baseSlot π μ edge base neighbor label p.1 p.2 t ∂ν
    avg (pair μ μ) score ≤
      _root_.PlanarUnitDistances.Flanks.offAvg μ.val score+
        2*(width ν (common π)+baseExceptionWidth π ν label base)*(∑i,(μ.val i)^2) := by
  intro score
  let W := 2*(width ν (common π)+baseExceptionWidth π ν label base)
  change avg (pair μ μ) score ≤ _ + W*∑i,(μ.val i)^2
  have one (i j : I) : μ.val i*μ.val j*score (i,j) ≤
      offWeight μ.val (i,j)*score (i,j)+(if i=j then W*(μ.val i)^2 else 0) := by
    by_cases e : i=j
    · subst j
      simp only [offWeight,ite_true,zero_mul,zero_add,pow_two]
      rw [mul_comm W]
      exact mul_le_mul_of_nonneg_left (base_diagonal_upper π ν μ edge base neighbor label i)
        (mul_nonneg (μ.nonneg _) (μ.nonneg _))
    · simp [offWeight,e]
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun j _ => one i j))
  unfold avg pair offAvg
  simp only [Fintype.sum_prod_type]
  simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true,←Finset.mul_sum] using h

end
end OAI.PlanarUnitDistances.PhysicalLevels
