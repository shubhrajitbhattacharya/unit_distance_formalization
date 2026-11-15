import PlanarUnitDistances.Counting
import PlanarUnitDistances.Constants
import PlanarUnitDistances.Heights

/-! The exact unit-distance bound and the labeled graphs used in its proof. -/
open OAI.PlanarUnitDistances
open Filter
open scoped Topology

namespace PlanarUnitDistances
noncomputable section

/-- Theorem A, including the absolute-constant quantifier. -/
def TheoremA : Prop := PowerSaving exactGap


def AlgebraicPoints (P : Finset Plane) : Prop := ∀ p ∈ P, ∀ k, IsAlgebraic ℚ (p k)

abbrev planeEdges := Finset (Plane × Plane)

/-- All the conditions on the geometric graph in geom:organized at its most
permissive rectangle tolerance, η = 1/(324 B). In particular the labels are
not required to come from a prescribed center after they are assigned. -/
structure AdmissibleGraph (n : ℕ) (K : Type) [Field K] [NumberField K] where
  embedding : K →+* ℂ
  points : Finset Plane
  algebraic : AlgebraicPoints points
  point_bound : points.card ≤ n
  edges : planeEdges
  endpoints : ∀ e ∈ edges, e.1 ∈ points ∧ e.2 ∈ points
  label : Plane → Plane → K
  scale : ℝ
  scale_bound : 12 * (2:ℝ)^111 ≤ scale
  nonzero : ∀ p r, (p,r) ∈ edges → label p r ≠ 0
  chord : ∀ p r, (p,r) ∈ edges →
    ((dist p r ^ 2 : ℝ) : ℂ) = 2 - embedding (label p r) - (embedding (label p r))⁻¹
  large_height : ∀ p r, (p,r) ∈ edges → scale/3 ≤ weilHeight (label p r)
  rectangle : ∀ p p' r r', (p,r) ∈ edges → (p',r') ∈ edges →
    (p,r') ∈ edges → (p',r) ∈ edges →
    weilHeight ((label p r * label p' r') / (label p r' * label p' r)) ≤ scale / (324*2^111)
  circle : ∀ p r, (p,r) ∈ edges → ∀ c : Plane, dist p c = 1 → dist r c = 1 →
    (((points.filter fun x => dist x c = 1).card : ℕ) : ℝ) < (n:ℝ) ^ (9/10:ℝ)


def incidenceScale (n : ℕ) : ℝ := (n:ℝ) ^ (1/3:ℝ)


end
end PlanarUnitDistances
