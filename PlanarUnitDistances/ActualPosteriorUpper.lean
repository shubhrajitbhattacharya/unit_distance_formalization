import PlanarUnitDistances.GraphBaseUpper
import PlanarUnitDistances.SupportedBaseSlots
import PlanarUnitDistances.PositiveIncidence

namespace PlanarUnitDistances.UniformPhysical
open Finset Set MeasureTheory NumberField OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open CommonFieldModel FiniteLaw FiniteStarCoupling TemplateCoupling CommonTemplate PhysicalLevels StarScore Flanks
open Real (log)
open scoped Classical
noncomputable section
variable {P Q : Finset CommonFieldModel.Plane} {I : Type} [Fintype I]

/-- The off-diagonal integral for the original conditional law on its
whole index set, using the original graph for the physical records. -/
def OriginalBaseUpper (M : Model P Q) (he : 0 < incidences P Q) (μ : Law I)
    (edge : I→P×Q) (base : P⊕Q) (neighbor : I→P⊕Q) (label : Record P Q→Finset (P⊕Q)×Finset (P⊕Q))
    (az aw : InfinitePlace M.field→ℝ×ℝ) : Prop :=
  let G := unitEdgeLaw he
  let ν := fullMeasure (unitRows P Q) M.z M.w az aw
  offAvg μ.val (fun ij => ∫t,baseSlot G μ edge base neighbor label ij.1 ij.2 t ∂ν) ≤
    (∫t,variation μ (fun i => t.bit (edge i).1 (edge i).2) ∂commonLaw G ν)/15+2*log 2

/-- A supported physical neighbor law can assign zero mass to other
vertices. All geometric hypotheses are needed only on positive atoms. -/
theorem supported_base_upper (M : Model P Q) (he : 0 < incidences P Q) (μ : Law I)
    (edge : I→P×Q) (base : P⊕Q) (neighbor : I→P⊕Q) (label : Record P Q→Finset (P⊕Q)×Finset (P⊕Q))
    (az aw : InfinitePlace M.field→ℝ×ℝ)
    (mem : ∀i : PositiveAtom μ,(edge i.val).1 ∈ unitRows P Q (edge i.val).2)
    (ends : ∀i : PositiveAtom μ,(neighbor i.val=.inl (edge i.val).1 ∧ base=.inr (edge i.val).2) ∨
      (neighbor i.val=.inr (edge i.val).2 ∧ base=.inl (edge i.val).1))
    (inj : Function.Injective (fun i : PositiveAtom μ => M.z (neighbor i.val)))
    (unit : ∀i : PositiveAtom μ,(M.z (neighbor i.val)-M.z base)*(M.w (neighbor i.val)-M.w base)=1) :
    OriginalBaseUpper M he μ edge base neighbor label az aw := by
  let G := unitEdgeLaw he
  let ν := fullMeasure (unitRows P Q) M.z M.w az aw
  have b : offAvg (onPositive μ).val (fun ij => ∫t,baseSlot G (onPositive μ) (fun i => edge i.val)
        base (fun i => neighbor i.val) label ij.1 ij.2 t ∂ν) ≤
      (∫t,variation (onPositive μ) (fun i => t.bit (edge i.val).1 (edge i.val).2) ∂commonLaw G ν)/15+2*log 2 :=
    graph_base_upper (unitRows P Q) M.z M.w G (onPositive μ)
      (fun i => edge i.val) base (fun i => neighbor i.val) label az aw mem ends inj unit
  rw [off_base_onPositive G ν μ edge base neighbor label] at b
  have each (t : Record P Q) : variation (onPositive μ) (fun i => t.bit (edge i.val).1 (edge i.val).2)=
      variation μ (fun i => t.bit (edge i).1 (edge i).2) := onPositive_variation μ (fun i => t.bit (edge i).1 (edge i).2)
  simpa only [OriginalBaseUpper, each, G, ν] using b

theorem center_posterior_upper (M : Model P Q) (he : 0 < incidences P Q) (q : Q)
    (hq : 0<(right (unitEdgeLaw he)).val q) (label : Record P Q→Finset (P⊕Q)×Finset (P⊕Q))
    (az aw : InfinitePlace M.field→ℝ×ℝ) :
    OriginalBaseUpper M he (col (unitEdgeLaw he) q) (fun p => (p,q)) (.inr q) Sum.inl label az aw := by
  have mem := positive_col_incidence he q hq
  exact supported_base_upper M he _ _ _ _ label az aw mem (fun _ => Or.inl ⟨rfl,rfl⟩)
    (fun _ _ h => Subtype.ext (M.point_injective h)) (fun p => M.unit_identity p.val q (mem_filter.mp (mem p)).2)

theorem point_posterior_upper (M : Model P Q) (he : 0 < incidences P Q) (p : P)
    (hp : 0<(left (unitEdgeLaw he)).val p) (label : Record P Q→Finset (P⊕Q)×Finset (P⊕Q))
    (az aw : InfinitePlace M.field→ℝ×ℝ) :
    OriginalBaseUpper M he (row (unitEdgeLaw he) p) (fun q => (p,q)) (.inl p) Sum.inr label az aw := by
  have mem := positive_row_incidence he p hp
  exact supported_base_upper M he _ _ _ _ label az aw mem (fun _ => Or.inr ⟨rfl,rfl⟩)
    (fun _ _ h => Subtype.ext (M.center_injective h)) (fun q => reverse_unit M (mem q))

theorem template_posterior_upper {T : Type} [Fintype T]
    (M : Model P Q) (he : 0 < incidences P Q) (a : Q→Law T) (j : T) (p : P)
    (hp : 0<(templates (unitEdgeLaw he) a).val j*(left (slice (unitEdgeLaw he) a j)).val p)
    (label : Record P Q→Finset (P⊕Q)×Finset (P⊕Q)) (az aw : InfinitePlace M.field→ℝ×ℝ) :
    OriginalBaseUpper M he (row (slice (unitEdgeLaw he) a j) p) (fun q => (p,q)) (.inl p) Sum.inr label az aw := by
  have mem := positive_slice_incidence he a j p hp
  exact supported_base_upper M he _ _ _ _ label az aw mem (fun _ => Or.inr ⟨rfl,rfl⟩)
    (fun _ _ h => Subtype.ext (M.center_injective h)) (fun q => reverse_unit M (mem q))

end
end PlanarUnitDistances.UniformPhysical


