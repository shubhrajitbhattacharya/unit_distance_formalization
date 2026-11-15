import PlanarUnitDistances.ResearchRecordAgreement
import PlanarUnitDistances.UniformPhysical

namespace PlanarUnitDistances.ResearchPhysical
open OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence CommonFieldModel
open Competition.IncidencePiece PhysicalLevels CommonTemplate CrossStructure FiniteLaw RareScore
open Finset FiniteStarCoupling MeasureTheory Set NumberField UniformNormalization UniformPhysical
open scoped Classical
noncomputable section
variable {P Q : Finset Competition.Plane}

/-- The two original constructions use the same normalized interval
integrals whenever their per-record integrands agree. -/
theorem integral_of_record_agreement (M : Model P Q) (u : InfinitePlace M.field → ℝ)
    (f : CoordinateLevel (toPiece M).Label → ℝ) (g : Record P Q → ℝ)
    (eq : ∀b t,RecordAgreement M b t → f b=g t) :
    let r := profileRadius (unitRows P Q) M.z M.w
    (toPiece M).placeIntegral (primes (unitRows P Q) M.z M.w) (fun v => -r v) r u f =
      ∫t, g t ∂fullMeasure (unitRows P Q) M.z M.w (fun v => (u v,u v)) (fun v => (u v,u v)) := by
  have a (v : InfinitePlace M.field) (s : ℝ) := eq _ _ (arch_agreement M v (u v,u v) (u v,u v) s)
  have k (v : FinitePlace M.field) (s : ℝ) := eq _ _ (finite_agreement M v s)
  dsimp only
  unfold fullMeasure placeIntegral
  rw [integral_measure]; simp_rw [a,k]

theorem inconsistency_integral_eq (M : Model P Q) (he : 0 < incidences P Q) (u : InfinitePlace M.field → ℝ) :
    let r := profileRadius (unitRows P Q) M.z M.w
    (toPiece M).placeIntegral (primes (unitRows P Q) M.z M.w) (fun v => -r v) r u (toPiece M).inconsistentMass =
      ∫t,inconsistency (incidenceLaw P Q he) t.bit t.x t.y
        ∂fullMeasure (unitRows P Q) M.z M.w (fun v => (u v,u v)) (fun v => (u v,u v)) :=
  integral_of_record_agreement M u _ _ (fun _ _ a => (a.rare_masses he).2)

end
end PlanarUnitDistances.ResearchPhysical
