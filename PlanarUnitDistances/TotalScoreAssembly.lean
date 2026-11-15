import PlanarUnitDistances.AveragedBaseSlots
import PlanarUnitDistances.BaseScoreAverage
import PlanarUnitDistances.FullScoreComparison

namespace OAI.PlanarUnitDistances.PhysicalLevels
open Finset MeasureTheory FiniteLaw FiniteStarCoupling TemplateCoupling StarScore
open _root_.PlanarUnitDistances.Flanks _root_.PlanarUnitDistances.ComparisonConstants
open scoped Classical
noncomputable section
variable {P Q I T : Type*} [Fintype P] [Fintype Q] [Fintype I] [Fintype T]

/-- The distinct-neighbor score inequality with the conditional law at the
specified base and the original law for the classification of levels. -/
def OffDiagonalBound (π : Law (P×Q)) (ν : Measure (Record P Q)) (μ : Law I)
    (edge : I → P×Q) (base : P⊕Q) (neighbor : I → P⊕Q)
    (l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)) : Prop :=
  offAvg μ.val (fun ij => ∫t,baseSlot π μ edge base neighbor l ij.1 ij.2 t ∂ν) ≤
    (∫t,variation μ (fun i => t.bit (edge i).1 (edge i).2) ∂commonLaw π ν)/15 + 2*Real.log 2

/-- Summing the three genuine conditional experiments, including zero-mass
bases and repeated neighbors, yields the inequalities of the manuscript. -/
theorem total_of_base_bounds (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν]
    (a : Q → Law T) (l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q))
    (qoff : ∀q,0 < (right π).val q → OffDiagonalBound π ν (col π q) (fun p => (p,q)) (.inr q) Sum.inl l)
    (poff : ∀p,0 < (left π).val p → OffDiagonalBound π ν (row π p) (fun q => (p,q)) (.inl p) Sum.inr l)
    (toff : ∀u p,0 < (templates π a).val u*(left (slice π a u)).val p →
      OffDiagonalBound π ν (row (slice π a u) p) (fun q => (p,q)) (.inl p) Sum.inr l)
    (qdiag : 2*Real.log 2+avg (right π) (fun q =>
      2*(width ν (common π)+baseExceptionWidth π ν l (.inr q))*(∑p,((col π q).val p)^2))≤dy 144*scale π ν)
    (pdiag : 2*Real.log 2+avg (left π) (fun p =>
      2*(width ν (common π)+baseExceptionWidth π ν l (.inl p))*(∑q,((row π p).val q)^2))≤dy 144*scale π ν)
    (tdiag : 2*Real.log 2+∑p,2*(width ν (common π)+baseExceptionWidth π ν l (.inl p))*
      (∑u,(templates π a).val u*(left (slice π a u)).val p*(∑q,((row (slice π a u) p).val q)^2))
      ≤dy 144*scale π ν) : TotalScoreComparison π ν a l := by
  constructor
  · rw [center_integrated_slots]
    exact average_base_scores π ν (right π) (col π) (fun q p => (p,q)) Sum.inr
      (fun _ => Sum.inl) l _ qoff qdiag
  · rw [point_integrated_slots]
    exact average_base_scores π ν (left π) (row π) (fun p q => (p,q)) Sum.inl
      (fun _ => Sum.inr) l _ poff pdiag
  · let β := dependent (templates π a) (fun u => left (slice π a u))
    let μ (b : T×P) := row (slice π a b.1) b.2
    let C (p : P) := 2*(width ν (common π)+baseExceptionWidth π ν l (.inl p))
    have diag : 2*Real.log 2+avg β (fun b => C b.2*(∑q,((μ b).val q)^2)) ≤ dy 144*scale π ν := by
      apply le_trans (le_of_eq (congrArg (2*Real.log 2+·) ?_)) tdiag
      unfold avg β dependent
      rw [Fintype.sum_prod_type,Finset.sum_comm]
      apply sum_congr rfl; intro p _
      rw [mul_sum]; apply sum_congr rfl; intro u _
      dsimp only [μ,C]; ring
    have h := average_base_scores π ν β μ (fun b q => (b.2,q)) (fun b => Sum.inl b.2)
      (fun _ => Sum.inr) l _ (fun b hb => toff b.1 b.2 hb) diag
    rw [list_integrated_slots]
    simpa only [β,μ,dependent_avg,VP] using h

end
end OAI.PlanarUnitDistances.PhysicalLevels
