import PlanarUnitDistances.ResearchDominantTransport
import PlanarUnitDistances.ResearchInconsistencyIntegral
import PlanarUnitDistances.RareMassBound
import PlanarUnitDistances.ArithmeticTailMeans

namespace PlanarUnitDistances.ResearchPhysical
open OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence CommonFieldModel
open Competition.IncidencePiece PhysicalLevels CommonTemplate CrossStructure FiniteLaw RareScore
open Finset FiniteStarCoupling MeasureTheory Set NumberField UniformNormalization UniformPhysical
open scoped Classical
noncomputable section
variable {P Q : Finset Competition.Plane}


/-- X, the expected exceptional point width on the original uniform
edge, equals X in the posterior comparison on its literal measure. -/
theorem exceptional_point_mean_eq (M : Model P Q) (he : 0 < incidences P Q) (u : InfinitePlace M.field → ℝ)
    (d : CoordinateLevel (toPiece M).Label → (toPiece M).Label)
    (c : Record P Q → Finset (P⊕Q)×Finset (P⊕Q))
    (hd : ∀b,(toPiece M).goodRare b → (toPiece M).dominantAt b (d b))
    (hc : ∀t∈PhysicalLevels.goodRare (incidenceLaw P Q he),
      pointException (incidenceLaw P Q he) (rareBit (incidenceLaw P Q he) t) (c t) t.x+
        centerException (incidenceLaw P Q he) (rareBit (incidenceLaw P Q he) t) (c t) t.y≤
      2*(minority (incidenceLaw P Q he) t+inconsistency (incidenceLaw P Q he) t.bit t.x t.y)) :
    let r := profileRadius (unitRows P Q) M.z M.w
    let π := incidenceLaw P Q he
    let ν := fullMeasure (unitRows P Q) M.z M.w (fun v => (u v,u v)) (fun v => (u v,u v))
    (toPiece M).edgeMean (fun e => (toPiece M).vertexWidth (primes (unitRows P Q) M.z M.w)
      (fun v => -r v) r u d e.1)=pointWidth π ν (rareBit π) c := by
  let G := toPiece M
  let π := incidenceLaw P Q he
  dsimp only
  rw [←pointWidth_integral,←integral_indicator (Set.toFinite _).measurableSet]
  unfold vertexWidth
  rw [edgeMean_placeIntegral]
  apply integral_of_record_agreement
  intro b t H
  by_cases good : G.goodRare b
  · have gt := (H.good_iff he).mp good
    rw [Set.indicator_of_mem gt]
    let A (e : Competition.Plane×Competition.Plane) := b.selected e.1≠d b
    have rep : (fun e : Competition.Plane×Competition.Plane => G.endpointWidth d e.1 b)=
        fun e => @ite ℝ (A e) (Classical.propDecidable _) 1 0 := by
      funext e
      by_cases z : b.selected e.1=d b <;> simp [A,endpointWidth,masked,good,CoordinateLevel.exceptionAt,z]
    rw [rep]
    exact (G.edgeMean_indicator A).trans
      (physical_event M he _ (fun e => exceptional (rareBit π t) (c t) (t.x e.1))
        (fun p _ _ => H.exception_iff he (d b) (c t) good (hd _ good) (hc _ gt) p))
  · have gt := mt (H.good_iff he).mpr good
    rw [Set.indicator_of_notMem gt]
    change G.edgeMean (fun e => G.endpointWidth d e.1 b)=0
    simp [endpointWidth,masked,good,edgeMean]

end
end PlanarUnitDistances.ResearchPhysical
