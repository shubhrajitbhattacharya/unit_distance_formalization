import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace PlanarUnitDistances.GenericAnchorField
open Set MvPolynomial
noncomputable section
variable {k E : Type*} [Field k] [Field E] [Algebra k E]

/-- Over the relative algebraic closure of the field of the four anchor
abscissas, all four anchor ordinates are already present and the eight
generic point abscissas remain jointly independent. -/
theorem anchor_coordinates (z : Fin 8 ⊕ Fin 4 → E) (w : Fin 4 → E)
    (ind : AlgebraicIndependent k z) (g : MvPolynomial (Fin 2) k) (ng : g≠0)
    (curve : ∀ j,aeval ![z (.inr j),w j] g=0) :
    let a := fun j => z (.inr j)
    let F := IntermediateField.adjoin k (range a)
    AlgebraicIndependent (_root_.algebraicClosure F E) (fun i => z (.inl i)) ∧
      ∀ j, w j ∈ _root_.algebraicClosure F E := by
  let a (j : Fin 4) := z (.inr j)
  let x (i : Fin 8) := z (.inl i)
  let F := IntermediateField.adjoin k (range a)
  have same : Sum.elim x a=z := by funext i; cases i <;> rfl
  have parts := AlgebraicIndependent.sumElim_iff.mp (same.symm ▸ ind)
  have left : AlgebraicIndependent F x := IntermediateField.algebraicIndependent_adjoin_iff.mpr parts.2
  refine ⟨left.algebraicClosure,fun j => mem_algebraicClosure_iff.mpr ?_⟩
  by_contra h
  have one : AlgebraicIndependent F (fun _ : Unit => w j) :=
    algebraicIndependent_unique_type_iff.mpr h
  have both := parts.1.sumElim (IntermediateField.algebraicIndependent_adjoin_iff.mp one)
  let e : Fin 2 → Unit ⊕ Fin 4 := ![.inr j,.inl ()]
  have inj : Function.Injective e := by intro i l; fin_cases i <;> fin_cases l <;> simp [e]
  have val : (Sum.elim (fun _ : Unit => w j) a) ∘ e = ![z (.inr j),w j] := by
    funext i; fin_cases i <;> rfl
  exact ng ((val ▸ both.comp e inj).eq_zero_of_aeval_eq_zero g (curve j))

end
end PlanarUnitDistances.GenericAnchorField
