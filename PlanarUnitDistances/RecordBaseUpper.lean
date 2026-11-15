import PlanarUnitDistances.RecordFlankProjection
import PlanarUnitDistances.RecordComparison

namespace OAI.PlanarUnitDistances.PhysicalLevels
open Set Finset MeasureTheory NumberField FiniteLaw FiniteStarCoupling CommonTemplate StarScore
open _root_.PlanarUnitDistances.Flanks _root_.PlanarUnitDistances.ComparisonConstants
open Real (log exp exp_log exp_zero)
open scoped Classical
noncomputable section
variable {P Q I K : Type*} [Fintype P] [Fintype Q] [Fintype I] [Field K] [NumberField K]

/-- The full, off-diagonal score at a single base in its original finite
record measure. All three kinds of experiment can have different
conditional laws μ; the level classification always uses π. -/
theorem record_base_upper (π : Law (P×Q)) (μ : Law I) (edge : I → P×Q)
    (base : P⊕Q) (neighbor : I → P⊕Q)
    (label : Record P Q → Finset (P⊕Q)×Finset (P⊕Q))
    (z w : P⊕Q → K) (az aw : InfinitePlace K → ℝ×ℝ) (F : Finset (FinitePlace K))
    (d : I → K) (nonzero : ∀i,d i≠0) (inj : Function.Injective d)
    (outside : ∀v : FinitePlace K,v∉F → ∀i,v (d i)=1)
    (A : ∀v : InfinitePlace K,LocalComparison μ.val d v.1 (dy 1800) (log 2))
    (B : ∀v : FinitePlace K,LocalComparison μ.val d v.1 (dy 1800) 0)
    (archId : ∀v,PlaceIdentification π μ edge base neighbor label (arch v (az v) (aw v) z w) d v.1 (log 2) (A v))
    (finId : ∀v,PlaceIdentification π μ edge base neighbor label (finite v z w) d v.1 0 (B v)) :
    let ν := measure F z w az aw (fun v => (A v).lo) (fun v => (A v).hi) (fun v => (B v).lo) (fun v => (B v).hi)
    offAvg μ.val (fun p => ∫t,baseSlot π μ edge base neighbor label p.1 p.2 t ∂ν) ≤
      (∫t,variation μ (fun i => t.bit (edge i).1 (edge i).2) ∂commonLaw π ν)/15 + 2*log 2 := by
  intro ν
  have half : dy 1800≤1/2 := (antitone (by decide : 1≤1800)).trans_eq (by norm_num [dy])
  have up := global_distinct_upper F μ.val μ.nonneg μ.total d nonzero inj outside half A B
  rw [offAvg_placeAverage] at up
  let a (p : I×I) := placeAverage F (fun v => (A v).pairScore p.1 p.2) (fun v => (B v).pairScore p.1 p.2)
  have each (p : I×I) (h : p.1≠p.2) : (∫t,baseSlot π μ edge base neighbor label p.1 p.2 t ∂ν)=a p := by
    unfold ν a placeAverage
    rw [integral_measure]
    simp only [(archId _).integral_slot _ _ h,(finId _).integral_slot _ _ h]
  have av : offAvg μ.val (fun p => ∫t,baseSlot π μ edge base neighbor label p.1 p.2 t ∂ν) = offAvg μ.val a := by
    unfold offAvg; apply sum_congr rfl; intro p _
    by_cases e : p.1=p.2
    · simp [offWeight,e]
    · exact congrArg (fun x => offWeight μ.val p*x) (each p e)
  have compare : (∫t,variation μ (fun i => t.bit (edge i).1 (edge i).2) ∂commonLaw π ν) =
      placeAverage F (fun v => (A v).comparison) (fun v => (B v).comparison) := by
    unfold commonLaw
    rw [←integral_indicator (Set.toFinite _).measurableSet]
    unfold ν placeAverage
    rw [integral_measure]
    simp only [Set.indicator,Set.mem_ofPred_eq]
    simp only [(archId _).integral_variation,(finId _).integral_variation]
  rw [av,compare]
  exact up

end
end OAI.PlanarUnitDistances.PhysicalLevels
