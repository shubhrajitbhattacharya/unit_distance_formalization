import PlanarUnitDistances.MeasuredSlots
import PlanarUnitDistances.RareDominant

namespace OAI.PlanarUnitDistances.PhysicalLevels
open Set Finset MeasureTheory FiniteLaw FiniteStarCoupling CommonTemplate StarScore
open _root_.PlanarUnitDistances.Flanks _root_.PlanarUnitDistances.ComparisonConstants
open scoped Classical
noncomputable section
variable {P Q I : Type*} [Fintype P] [Fintype Q] [Fintype I]

def vertexState (t : Record P Q) (x : P⊕Q) := Sum.elim t.x t.y x

/-- The summand on the original finite record space for one conditional
experiment. The common-level weight is evaluated at its own conditional
one-edge bias. -/
def baseSlot (π : Law (P×Q)) (μ : Law I) (edge : I → P×Q) (base : P⊕Q)
    (neighbor : I → P⊕Q) (label : Record P Q → Finset (P⊕Q)×Finset (P⊕Q))
    (i j : I) (t : Record P Q) :=
  let bits := fun i => t.bit (edge i).1 (edge i).2
  observedSlot (common π t) (good π t) (rareBit π t) (label t) (vertexState t base)
    (frequency μ bits) bits (fun i => vertexState t (neighbor i)) i j

end
end OAI.PlanarUnitDistances.PhysicalLevels
