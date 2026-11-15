import PlanarUnitDistances.GenericSolution
import PlanarUnitDistances.InfiniteAbscissas
import PlanarUnitDistances.GridElimination
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

namespace PlanarUnitDistances.Competition.GenericCurvePoint
open MvPolynomial GridElimination PublishedElimination
noncomputable section

/-- Density of concrete compatible positions on the given curve product
would supply a solution of all 140 lifted equations with twelve independent
abscissas. The inverse variables in the same system retain every required
inequality between tangent scalars. -/
theorem generic_grid_of_dense (f g : Poly₂) (pair : CurvePair f g)
    (dense : curveProduct f g ⊆ algebraicClosure {y | y∈curveProduct f g ∧ PositionSystem y}) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra ℂ E) (y : LiftCoord → E),
      (∀ i, aeval y (edgeList i)=0) ∧ (∀ j, aeval y (curveList f g j)=0) ∧
      AlgebraicIndependent ℂ (fun s : Slot => y (.inl (s,0))) := by
  let W := List.ofFn edgeList ++ List.ofFn (curveList f g)
  let S : Set P := {F | F∈W}
  let coords (s : Slot) : LiftCoord := .inl (s,0)
  have witness (p : MvPolynomial Slot ℂ) (hne : p≠0) :
      ∃ y : LiftCoord → ℂ, (∀ F∈S,eval y F=0) ∧ eval (y ∘ coords) p≠0 := by
    obtain ⟨x,hx,hp⟩ := product_abscissas pair p hne
    by_contra! no
    let F : MvPolynomial Coord ℂ := rename (fun s : Slot => (s,0)) p
    have vanish (q : GridTuple) (hq : q∈curveProduct f g ∧ PositionSystem q) : eval q F=0 := by
      have h : q ∈ (fun (y : LiftCoord → ℂ) i => y (.inl i)) '' equations W := by
        rw [show W=List.ofFn edgeList ++ List.ofFn (curveList f g) from rfl,projected_grid_locus]
        exact hq
      obtain ⟨y,hy,rfl⟩ := h
      simpa only [F,eval_rename,Function.comp_def,coords] using no y hy
    have h := dense hx F vanish
    exact hp (by simpa only [F,eval_rename,Function.comp_def] using h)
  obtain ⟨E,field,alg,y,sol,ind⟩ := GenericSolution.over_independent_coordinates coords S witness
  let _ : Field E := field
  let _ : Algebra ℂ E := alg
  refine ⟨E,field,alg,y,fun i => sol _ ((List.mem_append).mpr (Or.inl ?_)),
    fun j => sol _ ((List.mem_append).mpr (Or.inr ?_)),ind⟩
  · exact List.mem_ofFn.mpr ⟨i,rfl⟩
  · exact List.mem_ofFn.mpr ⟨j,rfl⟩

/-- The ambient solution may be chosen algebraically closed. This allows
later relative algebraic closures to contain all roots of the curve fibers. -/
theorem closed_generic_grid_of_dense (f g : Poly₂) (pair : CurvePair f g)
    (dense : curveProduct f g ⊆ algebraicClosure {y | y∈curveProduct f g ∧ PositionSystem y}) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra ℂ E) (_ : IsAlgClosed E) (y : LiftCoord → E),
      (∀ i, aeval y (edgeList i)=0) ∧ (∀ j, aeval y (curveList f g j)=0) ∧
      AlgebraicIndependent ℂ (fun s : Slot => y (.inl (s,0))) := by
  obtain ⟨M,field,alg,v,edges,curves,ind⟩ := generic_grid_of_dense f g pair dense
  let _ : Field M := field
  let _ : Algebra ℂ M := alg
  let E := AlgebraicClosure M
  let φ := IsScalarTower.toAlgHom ℂ M E
  refine ⟨E,inferInstance,inferInstance,inferInstance,φ ∘ v,?_,?_,ind.map' φ.injective⟩
  · intro i
    exact (comp_aeval_apply v φ _).symm.trans (by rw [edges,map_zero])
  · intro j
    exact (comp_aeval_apply v φ _).symm.trans (by rw [curves,map_zero])

end
end PlanarUnitDistances.Competition.GenericCurvePoint
