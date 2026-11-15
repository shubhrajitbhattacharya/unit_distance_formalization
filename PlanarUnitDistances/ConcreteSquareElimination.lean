import PlanarUnitDistances.ReducedDeformation
import Mathlib.Algebra.Polynomial.Bivariate

namespace PlanarUnitDistances.UniversalIncidence
open HomogeneousMacaulay MvPolynomial
noncomputable section
variable {q : ℕ} {k : Type*} [Field k]

abbrev State (q : ℕ) (k : Type*) [CommRing k] := MvPolynomial (Fin q) k

def dehom : MvPolynomial (Coord q) k →+* State q k :=
  eval₂Hom C (fun i : Coord q => i.elim 1 X)

def outputTest (j : Fin q) : Polynomial k →+* State q k := Polynomial.eval₂RingHom C (X j)

def inputForms (j : Fin q) (Q : Fin q → MvPolynomial (Coord q) k) (i : Coord q) :
    MvPolynomial (Coord q) k := i.elim (X (some j)) Q

def inputCoefficients (j : Fin q) (Q : Fin q → MvPolynomial (Coord q) k) :
    Coefficients q k := fun i m => (inputForms j Q i).coeff m.val

def deformedSquare (Q : Fin q → MvPolynomial (Coord q) k) (i : Fin q) : Polynomial (State q k) :=
  Polynomial.C (dehom (Q i))+Polynomial.X*Polynomial.C (X i^2)

theorem square_at_zero (Q : Fin q → MvPolynomial (Coord q) k) :
    (Ideal.span (Set.range (deformedSquare Q))).map (Polynomial.evalRingHom 0)=
      Ideal.span (Set.range (fun i => dehom (Q i))) := by
  rw [Ideal.map_span,←Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  simp [Function.comp,deformedSquare]

private theorem map_form {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (A : Coefficients q R) (i : Coord q) :
    MvPolynomial.map g (form A i)=form (fun t m => g (A t m)) i := by
  simp [form]

private theorem evaluate_swap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x y : S)
    (P : Polynomial (Polynomial R)) :
    Polynomial.eval₂RingHom (Polynomial.eval₂RingHom f x) y (Polynomial.Bivariate.swap P)=
      Polynomial.eval₂RingHom (Polynomial.eval₂RingHom f y) x P := by
  induction P using Polynomial.induction_on' with
  | add _ _ hp hq => simp only [map_add,hp,hq]
  | monomial n p =>
    induction p using Polynomial.induction_on' with
    | add p p' hp hp' => simp only [map_add,hp,hp']
    | monomial m c =>
      simp only [Polynomial.Bivariate.swap_monomial_monomial,Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_monomial]
      ring

private theorem roots_in_family {D : Type*} [CommRing D] (π : Polynomial (State q k) →+* D)
    (j : Fin q) (Q : Fin q → MvPolynomial (Coord q) k) (hom : ∀i,(Q i).IsHomogeneous 2)
    (roots : ∀i,π (deformedSquare Q i)=0) :
    let f := (π.comp Polynomial.C).comp (C : k →+* State q k)
    let x := fun i : Fin q => π (Polynomial.C (X i))
    ∀i, eval (fun o : Coord q => o.elim 1 x)
      (form (deformed (fun t m => f (inputCoefficients j Q t m)) (π Polynomial.X) (x j)) i)=0 := by
  let u := π.comp (Polynomial.C : State q k →+* _)
  let f := u.comp (C : k →+* State q k)
  let x := fun i : Fin q => u (X i)
  have hhom (i : Coord q) : (inputForms j Q i).IsHomogeneous (formDegree i) := by
    cases i with
    | none => exact isHomogeneous_X _ _
    | some i => exact hom i
  have val (i : Coord q) :
      eval (fun o : Coord q => o.elim 1 x) (form (fun t m => f (inputCoefficients j Q t m)) i)=
        u (dehom (inputForms j Q i)) := by
    rw [←map_form,show form (inputCoefficients j Q) i=inputForms j Q i from
      form_of_coeff (inputForms j Q) i (hhom i),←MvPolynomial.eval₂_eq_eval_map]
    unfold dehom
    rw [MvPolynomial.map_eval₂Hom]
    have point : (fun o : Coord q => o.elim 1 x)=(fun o : Coord q => u (o.elim 1 X)) := by
      funext o
      cases o <;> simp [x]
    rw [point]
    rfl
  change ∀ i : Coord q,eval (fun o : Coord q => o.elim 1 x)
    (form (deformed (fun t m => f (inputCoefficients j Q t m)) (π Polynomial.X) (x j)) i)=0
  intro i
  rw [form_deformed,map_add,map_mul,eval_C,map_pow,eval_X,val]
  cases i with
  | none => simp [inputForms,dehom,formDegree,x]
  | some i =>
    simpa [deformedSquare,inputForms,formDegree,x,u] using roots i

private theorem evaluation_zero_on_family {D : Type*} [CommRing D] (π : Polynomial (State q k) →+* D)
    (F : BlockMacaulay.Universal q) (relation : incidenceMap F=0)
    (j : Fin q) (Q : Fin q → MvPolynomial (Coord q) k) (hom : ∀i,(Q i).IsHomogeneous 2) :
    (∀i,π (deformedSquare Q i)=0) →
    π ((Polynomial.Bivariate.swap (deformationMap (inputCoefficients j Q) F)).eval₂
      (Polynomial.C.comp (outputTest j)) Polynomial.X)=0 := by
  intro root
  let u := π.comp (Polynomial.C : State q k →+* _)
  let f := u.comp (C : k →+* State q k)
  let x := fun i : Fin q => u (X i)
  have composition : π.comp (Polynomial.C.comp (outputTest j))=Polynomial.eval₂RingHom f (x j) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [outputTest,f,u]
    · simp [outputTest,x,u]
  let B := deformed (fun t m => f (inputCoefficients j Q t m)) (π Polynomial.X) (x j)
  have allRoots : ∀i,eval (fun o : Coord q => o.elim 1 x) (form B i)=0 := roots_in_family π j Q hom root
  have van := specializes_at_affine_point B x allRoots F relation
  rw [Polynomial.hom_eval₂,composition]
  change Polynomial.eval₂RingHom (Polynomial.eval₂RingHom f (x j)) (π Polynomial.X)
    (Polynomial.Bivariate.swap (deformationMap (inputCoefficients j Q) F))=0
  rw [evaluate_swap]
  change ((Polynomial.eval₂RingHom (Polynomial.eval₂RingHom f (π Polynomial.X)) (x j)).comp
      (deformationMap (inputCoefficients j Q))) F=0
  rw [deformation_evaluation]
  exact van

/-- The swapped deformation polynomial is in the literal ideal of the q
affine equations, after putting T equal to the prescribed state coordinate. -/
theorem concrete_deformation_membership (F : BlockMacaulay.Universal q) (relation : incidenceMap F=0)
    (j : Fin q) (Q : Fin q → MvPolynomial (Coord q) k) (hom : ∀i,(Q i).IsHomogeneous 2) :
    (Polynomial.Bivariate.swap (deformationMap (inputCoefficients j Q) F)).eval₂
      (Polynomial.C.comp (outputTest j)) Polynomial.X ∈ Ideal.span (Set.range (deformedSquare Q)) := by
  let I := Ideal.span (Set.range (deformedSquare Q))
  let π : Polynomial (State q k) →+* (Polynomial (State q k) ⧸ I) := Ideal.Quotient.mk I
  have rootI (i : Fin q) : π (deformedSquare Q i)=0 :=
    (Ideal.Quotient.eq_zero_iff_mem (I:=I)).mpr (Ideal.subset_span (Set.mem_range_self i))
  have zero := evaluation_zero_on_family (q:=q) (k:=k) (D:=Polynomial (State q k) ⧸ I) π F relation j Q hom rootI
  exact (Ideal.Quotient.eq_zero_iff_mem (I:=I)).mp zero

end
end PlanarUnitDistances.UniversalIncidence
