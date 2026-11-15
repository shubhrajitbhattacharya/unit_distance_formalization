import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace PlanarUnitDistances.GenericSolution
open MvPolynomial
open scoped nonZeroDivisors
noncomputable section

/-- If no nonzero polynomial in the indicated coordinates vanishes on every
concrete solution, then the same equations have an extension-field solution
with those coordinates jointly algebraically independent. -/
theorem over_independent_coordinates {k I V : Type} [Field k]
    (coord : I → V) (eqs : Set (MvPolynomial V k))
    (dense : ∀ p : MvPolynomial I k,p≠0 → ∃ y : V → k,
      (∀ f∈eqs,eval y f=0) ∧ eval (y ∘ coord) p≠0) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra k E) (y : V → E),
      (∀ f∈eqs,aeval y f=0) ∧ AlgebraicIndependent k (y ∘ coord) := by
  classical
  let P := MvPolynomial V k
  let v := rename (R := k) coord
  let S : Submonoid P := (nonZeroDivisors (MvPolynomial I k)).map v.toRingHom.toMonoidHom
  let J := Ideal.span eqs
  have disj : Disjoint (J:Set P) S := by
    apply Set.disjoint_left.mpr
    rintro _ h ⟨p,hp,rfl⟩
    obtain ⟨y,hy,ne⟩ := dense p (nonZeroDivisors.ne_zero hp)
    have ker : J≤RingHom.ker (eval y) := Ideal.span_le.mpr hy
    exact ne (by simpa [v,eval_rename] using (show eval y (v p)=0 from ker h))
  obtain ⟨q,hq,hJ,away⟩ := J.exists_le_prime_disjoint S disj
  let _ : q.IsPrime := hq
  let R := P ⧸ q
  let E := FractionRing R
  let φ : P →ₐ[k] E := (IsScalarTower.toAlgHom k R E).comp (Ideal.Quotient.mkₐ k q)
  let y (i : V) := φ (X i)
  have hom : aeval y=φ := by ext i; simp [y]
  have ker (f : P) : φ f=0 ↔ f∈q := by
    change algebraMap R E (Ideal.Quotient.mk q f)=0 ↔ _
    rw [←map_zero (algebraMap R E),(IsFractionRing.injective R E).eq_iff,Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨E,inferInstance,inferInstance,y,fun f hf => ?_,algebraicIndependent_iff.mpr ?_⟩
  · rw [hom]
    exact (ker _).mpr (hJ (Ideal.subset_span hf))
  · intro p hp
    by_contra ne
    apply Set.disjoint_left.mp away _ (show v p∈S from ⟨p,mem_nonZeroDivisors_of_ne_zero ne,rfl⟩)
    apply (ker _).mp
    rw [←hom]
    exact (aeval_rename coord y p).trans hp

end
end PlanarUnitDistances.GenericSolution
