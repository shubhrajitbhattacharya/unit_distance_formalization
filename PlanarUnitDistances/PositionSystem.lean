import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Fin.VecNotation

namespace PlanarUnitDistances.Competition
open MvPolynomial
open scoped ComplexConjugate
noncomputable section

abbrev Slot := Fin 8 ⊕ Fin 4
abbrev Coord := Slot × Fin 2
abbrev GridTuple := Coord → ℂ
abbrev Poly₂ := MvPolynomial (Fin 2) ℂ

def curveProduct (f g : Poly₂) : Set GridTuple :=
  {x | (∀ i, eval (fun d => x (.inl i,d)) f = 0) ∧ ∀ j, eval (fun d => x (.inr j,d)) g = 0}

/-- The two coordinates of each slot are null coordinates z,w. Velocities
in the dot product are Cartesian, even for complex positions. -/
def PositionSystem (x : GridTuple) : Prop :=
  ∃ (u μ : Fin 8 → Fin 4 → ℂ) (H : Fin 8 → Fin 2 → ℂ) (U : Fin 4 → Fin 2 → ℂ)
    (A : Fin 8 → ℂ) (a : Fin 4 → ℂ), ∀ i j,
    let dz := x (.inl i,0)-x (.inr j,0)
    let dw := x (.inl i,1)-x (.inr j,1)
    u i j * μ i j = 1 ∧ dz*dw = 2-u i j-μ i j ∧ A i ≠ a j ∧
      2*((dz+dw)/2*(H i 0-U j 0)+(dz-dw)/(2*Complex.I)*(H i 1-U j 1)) =
        (μ i j-u i j)*(A i-a j)

/-- The affine Zariski closure described by *all* polynomials that vanish
on the supplied set of concrete tuples. -/
def algebraicClosure (S : Set GridTuple) : Set GridTuple :=
  {x | ∀ F : MvPolynomial Coord ℂ, (∀ y ∈ S, eval y F=0) → eval x F=0}

def CurvePair (f g : Poly₂) : Prop :=
  (∀ h, h=f ∨ h=g → Irreducible h ∧
    (∀ z w : ℂ, eval ![z,w] h=0 ↔ eval ![conj w,conj z] h=0) ∧
    (∀ d : Fin 2, ∃ p r : Fin 2 → ℂ, eval p h=0 ∧ eval r h=0 ∧ p d≠r d)) ∧
  ¬∃ c : ℂ, ∀ p : Fin 2 → ℂ,
      (eval p f=0 ↔ (p 0-c)*(p 1-conj c)=1) ∧ (eval p g=0 ↔ (p 0-c)*(p 1-conj c)=1)


end
end PlanarUnitDistances.Competition
