import PlanarUnitDistances.GeometricLargeProfile
import PlanarUnitDistances.SurvivingGraph
import PlanarUnitDistances.Main

namespace PlanarUnitDistances.ProofAssembly
open Filter OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open UniformNormalization EdgeHeightScale
open scoped Topology Classical
noncomputable section

/-- All simultaneous estimates on the original directions, at the target
exponent, before any choice of surviving ordered pairs. -/
def LargePiece (t : ℝ) (P Q : Finset Plane) (M : CommonFieldModel.Model P Q) : Prop :=
  let g := 3*exactGap
  let a := 10000*g
  AlgebraicPoints P ∧
  t^(1+2*a-173*g) ≤ (P.card:ℝ) ∧ (P.card:ℝ) ≤ 2*t^(1+2*a) ∧
  (Q.card:ℝ) ≤ t^(2+a) ∧ t^(2+2*a-90*g) ≤ incidences P Q ∧
  (∀ p ∈ P, (27/100:ℝ)*t^(1-90*g) ≤ degree Q p ∧ degree Q p ≤ t^(1+10*g) ∧
    (27/50:ℝ)/P.card ≤ degree Q p/incidences P Q ∧
    degree Q p/incidences P Q ≤ t^(-1-2*a+100*g)) ∧
  t^(-1-2*a+100*g) ≤ t^(-1:ℝ) ∧
  (∀ q ∈ Q, (27/50:ℝ)*t^(a-90*g) ≤ degree P q ∧ degree P q ≤ t^(a+10*g) ∧
    (27/50:ℝ)/Q.card ≤ degree P q/incidences P Q) ∧
  (∀ A ⊆ P, ∀ B ⊆ Q, let z := (A.card:ℝ)/P.card*((B.card:ℝ)/Q.card)
    incidences A B/incidences P Q ≤ Real.sqrt z*(z^(1/25:ℝ)+t^(-150*g))) ∧
  unitWalkInformation P Q+1 ≤ 10200*g*Real.log t ∧
  let r := profileRadius (unitRows P Q) M.z M.w
  (2:ℝ)^2100 < profileScale (unitRows P Q) (incidences P Q) M.z (fun v => -r v) r


theorem dense_to_large_piece :
    ∀ᶠ t : ℝ in atTop, ∀ X : Finset Plane, (X.card:ℝ)=t^3 →
      t^(4-3*exactGap) ≤ ((orderedPairs X).card:ℝ) →
      ∃ (P Q : Finset Plane) (M : CommonFieldModel.Model P Q), LargePiece t P Q M :=
  dense_large_profile


end
end PlanarUnitDistances.ProofAssembly
