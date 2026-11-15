import PlanarUnitDistances.TripleLaw
import PlanarUnitDistances.Selection

namespace PlanarUnitDistances.Competition
open Finset Filter NumberField
open scoped Classical Topology
noncomputable section
variable {K : Type} [Field K] [NumberField K]

def tripleRatio (M : IncidencePiece K) (v : Triple M) : K :=
  (M.Z v.1.val-M.Z v.2.1.val)/(M.Z v.2.2.val-M.Z v.2.1.val)

/-- Both endpoint functions are fixed on the graph before the triple is drawn. -/
structure Scores (M : IncidencePiece K) where
  H : M.P → ℝ
  arch : M.P → InfinitePlace K → ℝ
  finite : M.P → FinitePlace K →₀ ℝ
  error : Triple M → ℝ

def Scores.width {M : IncidencePiece K} (d : Scores M) (v : Triple M) := d.H v.1+d.H v.2.2

def signedError {M : IncidencePiece K} (d : Scores M) (u : Triple M) : ℝ :=
  ((∑ v : InfinitePlace K, (v.mult:ℝ)*|Real.log (v (tripleRatio M u))-
    (d.arch u.2.2 v-d.arch u.1 v)|) +
   ∑ᶠ v : FinitePlace K, |Real.log (v (tripleRatio M u))-(d.finite u.2.2 v-d.finite u.1 v)|) /
     (Module.finrank ℚ K:ℝ)

/-- The three bounds for one physical triple law, with both pointwise
inequalities relating its width and error functions to the actual assigned edge directions. -/
structure MomentBounds (M : IncidencePiece K) (d : Scores M) : Prop where
  width_nn : ∀ x, 0 ≤ d.width x
  error_nn : ∀ x, 0 ≤ d.error x
  mean : 2*M.scale/203 < ∑ x, M.mass x*d.width x
  tail : (∑ x, M.mass x*(if 8*M.scale/eps<d.width x then d.width x else 0)) ≤
    (2:ℝ)^14/2^144*M.scale
  error : (∑ x, M.mass x*d.error x) ≤ (2:ℝ)^12/2^144*M.scale
  signed : ∀ x, 0<M.mass x → signedError d x ≤ d.error x
  unsigned : ∀ x, 0<M.mass x →
    |2*(Height.logHeight₁ (tripleRatio M x)/(Module.finrank ℚ K:ℝ))-d.width x| ≤ d.error x


end
end PlanarUnitDistances.Competition
