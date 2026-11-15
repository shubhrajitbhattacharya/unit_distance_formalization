import PlanarUnitDistances.Algebra
import PlanarUnitDistances.CurveReflection
import PlanarUnitDistances.Main
import PlanarUnitDistances.GridLocus

/-! A moving tangent to one complete grid yields its simultaneous differential
equations in Cartesian coordinates, including repeated positions. -/
namespace PlanarUnitDistances.MovingGrid
open OAI.PlanarUnitDistances
open Fibre CurveReflection
open scoped Classical ComplexConjugate
noncomputable section

variable {n : ℕ} {K : Type} [Field K] [NumberField K]
variable {I J : Type}

def cartPoint (p : Plane) : Fin 2 → ℂ := fun i => (p i : ℂ)

def ratio (G : AdmissibleGraph n K) (p r : Plane) : ℂ := G.embedding (G.label p r)

def signedRoot (G : AdmissibleGraph n K) (p r : Plane) : ℂ := (ratio G p r)⁻¹-ratio G p r

/-- One actual tangent to the fixed-quotient fibre, matching all positions
and assigned ratios in the given graph. The coefficients of rectangles are
their actual cross ratios by the constant terms of the displayed equations. -/
structure Lift (G : AdmissibleGraph n K) (p : I → Plane) (r : J → Plane) where
  rowBase : I
  colBase : J
  rowPos : I → DualNumber ℂ × DualNumber ℂ
  colPos : J → DualNumber ℂ × DualNumber ℂ
  u : I → J → DualNumber ℂ
  m : I → J → DualNumber ℂ
  coeff : I → J → ℂ
  system : GridEquations rowBase colBase rowPos colPos u m
    (fun i j => TrivSqZeroExt.inl (coeff i j))
  row_fst : ∀ i, position (rowPos i) = (cartPoint (p i) 0,cartPoint (p i) 1)
  col_fst : ∀ j, position (colPos j) = (cartPoint (r j) 0,cartPoint (r j) 1)
  ratio_fst : ∀ i j, (u i j).fst=ratio G (p i) (r j)
  moving : ∀ i j,(u i j).snd≠0

/-- The moving-tangent conclusion needed from the height theorem on all complete
rectangles of the indicated sizes. No point-injectivity requirement is imposed. -/
def Motion (G : AdmissibleGraph n K) : Prop :=
  ∀ (I J : Type) [Fintype I] [Fintype J] (p : I → Plane) (r : J → Plane),
    2 ≤ Fintype.card I → 2 ≤ Fintype.card J → (Fintype.card I ≤ 4 ∨ Fintype.card J ≤ 4) →
    (∀ i j, (p i,r j) ∈ G.edges) → Nonempty (Lift G p r)

/-- The differential and root identities for a single shared velocity assignment. -/
structure Equations (p : I → Plane) (r : J → Plane) (R : I → J → ℂ) where
  H : I → Fin 2 → ℂ
  U : J → Fin 2 → ℂ
  A : I → ℂ
  a : J → ℂ
  equation : ∀ i j,
    let x := cartPoint (p i) 0-cartPoint (r j) 0
    let y := cartPoint (p i) 1-cartPoint (r j) 1
    let d := x^2+y^2
    R i j ^ 2=d*(d-4) ∧
      2*(x*(H i 0-U j 0)+y*(H i 1-U j 1))=R i j*(A i-a j)
  velocity_ne : ∀ i j, A i ≠ a j

theorem Lift.equations {G : AdmissibleGraph n K} {p : I → Plane} {r : J → Plane}
    (L : Lift G p r) : Nonempty (Equations p r (fun i j => signedRoot G (p i) (r j))) := by
  obtain ⟨A,a,eq⟩ := moving_grid_differential L.rowBase L.colBase L.rowPos L.colPos L.u L.m
    L.coeff L.system L.moving
  have hInv (i j) : (L.m i j).fst = (ratio G (p i) (r j))⁻¹ := by
    have inv := congrArg TrivSqZeroExt.fst (L.system.inverse i j)
    simp only [TrivSqZeroExt.fst_mul,TrivSqZeroExt.fst_one,L.ratio_fst] at inv
    have hn := left_ne_zero_of_mul_eq_one inv
    apply mul_left_cancel₀ hn
    simpa [hn] using inv
  refine ⟨⟨(fun i => ![(velocity (L.rowPos i)).1,(velocity (L.rowPos i)).2]),
    (fun j => ![(velocity (L.colPos j)).1,(velocity (L.colPos j)).2]),A,a,?_,?_⟩⟩
  · intro i j
    have e := eq i j
    rw [L.row_fst,L.col_fst,hInv,L.ratio_fst] at e
    exact ⟨e.2.1,e.1⟩
  · exact fun i j => sub_ne_zero.mp (eq i j).2.2

/-- Transposing a grid uses the same assigned root. Both scalar velocities
change sign, so that the row-minus-column difference is preserved. -/
def Equations.transpose {p : I → Plane} {r : J → Plane} {R : I → J → ℂ}
    (e : Equations p r R) : Equations r p (fun j i => R i j) where
  H := e.U
  U := e.H
  A := fun j => -e.a j
  a := fun i => -e.A i
  equation j i := by
    obtain ⟨h₁,h₂⟩ := e.equation i j
    dsimp only at h₁ h₂ ⊢
    constructor
    · linear_combination h₁
    · linear_combination h₂
  velocity_ne j i := fun h => e.velocity_ne i j (neg_injective h).symm

theorem recover_cart (p : Plane) : GridLocus.cart (realPoint p) = cartPoint p := by
  funext j
  fin_cases j
  · change (zCoord p + conj (zCoord p))/2 = (p 0 : ℂ)
    apply Complex.ext <;> simp [zCoord]
  · change (zCoord p - conj (zCoord p))/(2*Complex.I) = (p 1 : ℂ)
    apply Complex.ext <;> simp [zCoord,Complex.div_re,Complex.div_im]
    ring

/-- The exact tuple predicate used by the exceptional-locus grid count,
on every ordered complete grid, including repeated positions. -/
theorem compatible {G : AdmissibleGraph n K} (motion : Motion G) (p : Fin 8 → Plane)
    (r : Fin 4 → Plane) (edges : ∀ i j, (p i,r j) ∈ G.edges) :
    GridLocus.compatibleTuple (GridLocus.join (realPoint ∘ p) (realPoint ∘ r)) := by
  obtain ⟨L⟩ := motion (Fin 8) (Fin 4) p r (by decide) (by decide) (Or.inr (by decide)) edges
  obtain ⟨e⟩ := L.equations
  refine ⟨(fun i j => ratio G (p i) (r j)),e.H,e.U,e.A,e.a,?_⟩
  intro i j
  change ratio G (p i) (r j) ≠ 0 ∧
    (zCoord (p i)-zCoord (r j))*(conj (zCoord (p i))-conj (zCoord (r j))) =
      2-ratio G (p i) (r j)-(ratio G (p i) (r j))⁻¹ ∧ _ ∧ _
  refine ⟨?_, ?_,e.velocity_ne i j,?_⟩
  · simpa only [ratio,map_zero] using G.embedding.injective.ne (G.nonzero _ _ (edges i j))
  · rw [←map_sub,Complex.mul_conj,zCoord_sub_normSq]
    exact G.chord _ _ (edges i j)
  · simpa only [GridLocus.join,Sum.elim_inl,Sum.elim_inr,Function.comp_apply,recover_cart,signedRoot]
      using (e.equation i j).2

end
end PlanarUnitDistances.MovingGrid
