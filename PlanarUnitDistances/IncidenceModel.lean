import PlanarUnitDistances.ContestStatement
import PlanarUnitDistances.Heights
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace PlanarUnitDistances.Competition
open Finset NumberField Filter
open scoped Classical Topology
noncomputable section

def z (p : Plane) : ℂ := ⟨p 0,p 1⟩

/-- The original unit edges, before a random embedding, normalization or deletion.
The same number field contains all coordinates used at all places. -/
structure IncidencePiece (K : Type) [Field K] [NumberField K] where
  P : Finset Plane
  Q : Finset Plane
  E : Finset (Plane × Plane)
  membership : E ⊆ P ×ˢ Q
  algebraic : ∀ p ∈ P ∪ Q, ∀ i, IsAlgebraic ℚ (p i)
  unit : ∀ e ∈ E, dist e.1 e.2 = 1
  embedding : K →+* ℂ
  imaginaryUnit : K
  imaginaryUnit_spec : embedding imaginaryUnit = Complex.I
  Z : Plane → K
  W : Plane → K
  coordinates : ∀ p ∈ P ∪ Q, embedding (Z p)=z p ∧ embedding (W p)=star (z p)

variable {K : Type} [Field K] [NumberField K]

def IncidencePiece.degreeP (M : IncidencePiece K) (p : Plane) := (M.Q.filter (fun q => (p,q)∈M.E)).card
def IncidencePiece.degreeQ (M : IncidencePiece K) (q : Plane) := (M.P.filter (fun p => (p,q)∈M.E)).card
def IncidencePiece.mu (M : IncidencePiece K) (p : Plane) : ℝ := (M.degreeP p:ℝ)/M.E.card
def IncidencePiece.kappa (M : IncidencePiece K) (q : Plane) : ℝ := (M.degreeQ q:ℝ)/M.E.card

/-- A triple is sampled by choosing a uniform edge (p,q) and then a uniform
neighbor r of that same q. Repeated endpoints are part of this law. -/
abbrev Triple (M : IncidencePiece K) := M.P × M.Q × M.P

def IncidencePiece.mass (M : IncidencePiece K) (v : Triple M) : ℝ :=
  if (v.1.val,v.2.1.val)∈M.E ∧ (v.2.2.val,v.2.1.val)∈M.E
  then 1/((M.E.card:ℝ)*(M.degreeQ v.2.1.val:ℝ)) else 0

def IncidencePiece.joint (M : IncidencePiece K) (p r : M.P) : ℝ := ∑ q : M.Q, M.mass (p,q,r)

def IncidencePiece.information (M : IncidencePiece K) : ℝ :=
  ∑ p : M.P, ∑ r : M.P, M.joint p r * Real.log (M.joint p r / (M.mu p.val*M.mu r.val))

/-- The distribution function of the signed edge threshold, averaged with
the original uniform edge law. Extending the level integral to all of ℝ leaves
its value unchanged since the minority mass vanishes outside the edge range. -/
def IncidencePiece.localWidth (M : IncidencePiece K) (v : K → ℝ) : ℝ :=
  ∫ s : ℝ, (let π : ℝ := ((M.E.filter fun e => s < -Real.log (v (M.Z e.1-M.Z e.2))).card:ℝ)/M.E.card; min π (1-π))

def IncidencePiece.scale (M : IncidencePiece K) : ℝ :=
  ((∑ v : InfinitePlace K, (v.mult:ℝ)*M.localWidth (fun x => v x)) +
   ∑ᶠ v : FinitePlace K, M.localWidth (fun x => v x)) / (Module.finrank ℚ K : ℝ)

def savingG : ℝ := 3*exactGap
def savingA : ℝ := 10000*savingG
def eps : ℝ := (2:ℝ)^(-(1800:ℝ))
def gamma : ℝ := 27/50

/-- Conditions on the actual winner of the density restriction, all on one
graph. Counting fractions in the rectangle estimate are unweighted. -/
structure Regular (M : IncidencePiece K) (t : ℝ) : Prop where
  point_min : t^(1+2*savingA-173*savingG) ≤ M.P.card
  point_max : (M.P.card:ℝ) ≤ 2*t^(1+2*savingA)
  center_max : (M.Q.card:ℝ) ≤ t^(2+savingA)
  size : t^(2+2*savingA-90*savingG) ≤ M.E.card
  point_degree : ∀ p ∈ M.P, (gamma/2)*t^(1-90*savingG) ≤ M.degreeP p ∧
    (M.degreeP p:ℝ) ≤ t^(1+10*savingG)
  center_degree : ∀ q ∈ M.Q, gamma*t^(savingA-90*savingG) ≤ M.degreeQ q ∧
    (M.degreeQ q:ℝ) ≤ t^(savingA+10*savingG)
  point_marginal : ∀ p ∈ M.P, gamma/M.P.card ≤ M.mu p ∧ M.mu p ≤ t^(-1-2*savingA+100*savingG)
  center_marginal : ∀ q ∈ M.Q, gamma/M.Q.card ≤ M.kappa q
  rectangle : ∀ (A B : Finset Plane), A ⊆ M.P → B ⊆ M.Q →
    let u := (A.card:ℝ)/M.P.card
    let v := (B.card:ℝ)/M.Q.card
    ((M.E ∩ (A×ˢB)).card:ℝ)/M.E.card ≤ Real.sqrt (u*v)*((u*v)^(1/25:ℝ)+t^(-150*savingG))
  information : M.information + 1 ≤ 10200*savingG*Real.log t


end
end PlanarUnitDistances.Competition
