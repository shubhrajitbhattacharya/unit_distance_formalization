import PlanarUnitDistances.CurveReflection
import PlanarUnitDistances.GridObstruction

namespace PlanarUnitDistances.GridLocus
open MvPolynomial
open scoped Classical ComplexConjugate
noncomputable section

abbrev Point := Fin 2 → ℂ
abbrev PlanePoly := MvPolynomial (Fin 2) ℂ
abbrev Tuple := (Fin 8 ⊕ Fin 4) → Point
abbrev TuplePoly := MvPolynomial ((Fin 8 ⊕ Fin 4) × Fin 2) ℂ

/-- z,w are the two independent complex plane coordinates. -/
def curveProduct (f g : PlanePoly) (u : Tuple) : Prop :=
  (∀ i, eval (u (.inl i)) f = 0) ∧ ∀ j, eval (u (.inr j)) g = 0

/-- The full hypotheses on the two curves before considering generic tuples. -/
def curvePair (f g : PlanePoly) : Prop :=
  (∀ h ∈ ({f,g} : Finset PlanePoly), Irreducible h ∧
    (∀ p, eval p h = 0 ↔ eval (CurveReflection.reflectPoint p) h = 0) ∧
    ∀ d : Fin 2, ∃ p r : Point, eval p h=0 ∧ eval r h=0 ∧ p d ≠ r d) ∧
  ¬∃ c : ℂ, ∀ p : Point,
    (eval p f=0 ↔ (p 0-c)*(p 1-conj c)=1) ∧
    (eval p g=0 ↔ (p 0-c)*(p 1-conj c)=1)

/-- Recover Cartesian coordinates BEFORE taking the manuscript's dot product. -/
def cart (p : Point) : Point := ![(p 0+p 1)/2,(p 0-p 1)/(2*Complex.I)]

def compatibleTuple (u : Tuple) : Prop :=
  ∃ (ratio : Fin 8 → Fin 4 → ℂ) (H : Fin 8 → Point) (U : Fin 4 → Point)
    (A : Fin 8 → ℂ) (a : Fin 4 → ℂ), ∀ i j,
      let p := u (.inl i)
      let r := u (.inr j)
      ratio i j ≠ 0 ∧ (p 0-r 0)*(p 1-r 1)=2-ratio i j-(ratio i j)⁻¹ ∧
      A i ≠ a j ∧ 2*((cart p 0-cart r 0)*(H i 0-U j 0)+
        (cart p 1-cart r 1)*(H i 1-U j 1))=((ratio i j)⁻¹-ratio i j)*(A i-a j)

def separates (f g : PlanePoly) (Q : TuplePoly) : Prop :=
  (∀ u, curveProduct f g u → compatibleTuple u →
    eval (fun e => u e.1 e.2) Q = 0) ∧
    ∃ u, curveProduct f g u ∧ eval (fun e => u e.1 e.2) Q ≠ 0

/-- geom:proper in its equivalent affine separating-polynomial formulation.
The witness for nonvanishing is on the actual product of the two curves. -/
def ProperGridLocus : Prop := ∀ f g, curvePair f g → ∃ Q, separates f g Q


/-- The ordered tuple used in the position-locus statement. -/
def join (p : Fin 8 → Point) (r : Fin 4 → Point) : Tuple := Sum.elim p r


end
end PlanarUnitDistances.GridLocus
