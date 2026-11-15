import PlanarUnitDistances.Geometry
import PlanarUnitDistances.IncidenceEntropy

/-! The common-center bound and the information estimate on Euclidean
unit-incidence graphs, including graphs formed by deleting edges. -/

noncomputable section

namespace PlanarUnitDistances

open OAI.PlanarUnitDistances
open OAI.PlanarUnitDistances.FiniteInformation
open scoped ComplexConjugate

theorem zCoord_injective : Function.Injective zCoord := by
  intro p q h
  ext i
  fin_cases i
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h

/-- Two distinct real Euclidean points have at most two common unit centers
in any finite set of injectively labelled centers. Subgraphs are permitted. -/
theorem planar_common_centers_le_two {Q : Type*} (s : Finset Q) (center : Q → Plane)
    (hc : Set.InjOn center (s : Set Q)) {p r : Plane} (hpr : p ≠ r)
    (hp : ∀ q ∈ s, dist p (center q) = 1) (hr : ∀ q ∈ s, dist r (center q) = 1) :
    s.card ≤ 2 := by
  apply common_centers_le_two s (fun q ↦ zCoord (center q)) (fun q ↦ conj (zCoord (center q)))
    (fun _ hx _ hy hh ↦ hc hx hy (zCoord_injective hh))
    (wp := conj (zCoord p)) (wr := conj (zCoord r)) (zCoord_injective.ne hpr.symm)
  · exact fun q hq ↦ unit_edge_reciprocal (hp q hq)
  · exact fun q hq ↦ unit_edge_reciprocal (hr q hq)

/-- Exact codegree input of the graph entropy theorem. The neighborhoods
may retain any subset of the geometric unit edges. -/
theorem euclidean_unit_graph_codegree {P Q : Type*} [Fintype Q] [DecidableEq P]
    (point : P → Plane) (center : Q → Plane)
    (hp : Function.Injective point) (hc : Function.Injective center)
    (neighbors : Q → Finset P)
    (hunit : ∀ q i, i ∈ neighbors q → dist (point i) (center q) = 1)
    (i j : P) (hij : i ≠ j) :
    (Finset.univ.filter fun q ↦ i ∈ neighbors q ∧ j ∈ neighbors q).card ≤ 2 := by
  apply planar_common_centers_le_two _ center hc.injOn (hp.ne hij)
  · intro q hq
    exact hunit q _ (Finset.mem_filter.mp hq).2.1
  · intro q hq
    exact hunit q _ (Finset.mem_filter.mp hq).2.2

/-- The two-edge information inequality for the Euclidean unit graph, with
centers sampled in proportion to degree and their neighbors uniformly and
independently. The asymptotic cardinality and degree bounds are separate inputs. -/
theorem euclidean_unit_graph_mutual_information {P Q : Type*} [Fintype P] [Nonempty P]
    [Fintype Q] [DecidableEq P] (point : P → Plane) (center : Q → Plane)
    (hp : Function.Injective point) (hc : Function.Injective center)
    (neighbors : Q → Finset P)
    (hunit : ∀ q i, i ∈ neighbors q → dist (point i) (center q) = 1)
    {d : ℝ} (hd : 0 < d) (hmin : ∀ q, d ≤ ((neighbors q).card : ℝ))
    {e : ℝ} (he : 0 < e) (hsum : ∑ q, ((neighbors q).card : ℝ) = e)
    (hpoint : ∀ i, ∃ q, i ∈ neighbors q) :
    let κ := fun q ↦ ((neighbors q).card : ℝ) / e
    let w := fun q i ↦ if i ∈ neighbors q then ((neighbors q).card : ℝ)⁻¹ else 0
    KL (wedge κ w) (fun z ↦ marginal κ w z.1 * marginal κ w z.2) ≤
      2 * Real.log (Fintype.card P) - (1 - (Fintype.card Q : ℝ)/e) * Real.log (e*d/2) :=
  graph_wedge_mutual_information_bound neighbors hd hmin
    (euclidean_unit_graph_codegree point center hp hc neighbors hunit) he hsum hpoint

end PlanarUnitDistances
