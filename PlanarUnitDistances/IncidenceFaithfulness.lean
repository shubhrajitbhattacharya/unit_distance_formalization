import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Tactic

namespace PlanarUnitDistances.UniversalIncidence
open Polynomial MvPolynomial
noncomputable section

/-- If a substitution fixes the deformation variable and is injective on
the special fiber, it is injective on polynomial families. Divide out
successive powers of the deformation variable from a putative relation. -/
theorem injective_polynomial_lift {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    (f : Polynomial R →+* Polynomial S) (g : R →+* S)
    (hg : Function.Injective g) (var : f Polynomial.X=Polynomial.X)
    (fiber : ∀p,(f p).coeff 0=g (p.coeff 0)) : Function.Injective f := by
  have zero (n : ℕ) (p : Polynomial R) (deg : p.natDegree=n) (hp : f p=0) : p=0 := by
    induction n using Nat.strong_induction_on generalizing p with
    | h n ih =>
      have base : p.coeff 0=0 := hg (by rw [←fiber,hp,Polynomial.coeff_zero,map_zero])
      by_cases hn : n=0
      · rw [Polynomial.eq_C_of_natDegree_eq_zero (deg.trans hn),base,Polynomial.C_0]
      · have mul : Polynomial.X*p.divX=p := by simpa only [base,Polynomial.C_0,add_zero] using p.X_mul_divX_add
        have inside : f p.divX=0 := by
          have z := (map_mul f Polynomial.X p.divX).symm.trans ((congrArg f mul).trans hp)
          rw [var] at z
          exact (mul_eq_zero.mp z).resolve_left Polynomial.X_ne_zero
        have lt : p.divX.natDegree<n := by rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one,deg];omega
        rw [←mul,ih _ lt p.divX rfl inside,mul_zero]
  intro p q he
  exact sub_eq_zero.mp (zero _ (p-q) rfl (by rw [map_sub,he,sub_self]))

variable {k α ι : Type*} [CommRing k] [IsDomain k]
abbrev ChartRing (k α ι : Type*) [CommRing k] := MvPolynomial (α ⊕ ι) k

/-- A coefficient-parametrized system fixes all free parameters and sends
each remaining univariate coefficient to its reconstructed polynomial. -/
def chartMap (H : ι → ChartRing k α ι) : ChartRing k α ι →+* ChartRing k α ι :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Sum.elim (fun a=>MvPolynomial.X (.inl a)) H)

omit [IsDomain k] in
/-- Squaring only the state coordinates is injective: squaring the
remaining coordinates afterwards is the ordinary injective expansion. -/
theorem square_chart_injective :
    Function.Injective (chartMap (fun i : ι => (MvPolynomial.X (.inr i) : ChartRing k α ι)^2)) := by
  let G : ChartRing k α ι →+* ChartRing k α ι := MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim (fun a => MvPolynomial.X (.inl a)^2) (fun i => MvPolynomial.X (.inr i)))
  have comp : G.comp (chartMap (fun i : ι => (MvPolynomial.X (.inr i) : ChartRing k α ι)^2)) =
      (MvPolynomial.expand 2 (R:=k) (σ:=α ⊕ ι)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [G,chartMap]
    · rintro (a|i) <;> simp [G,chartMap]
  intro p q h
  apply MvPolynomial.expand_injective (by decide : 0<2)
  exact (RingHom.congr_fun comp p).symm.trans ((congrArg G h).trans (RingHom.congr_fun comp q))

/-- Freeze only the free coefficients at their diagonal values. -/
def center (d : α → k) : ChartRing k α ι →+* ChartRing k α ι :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim (fun a => MvPolynomial.C (d a)) (fun i => MvPolynomial.X (.inr i)))

/-- The coefficient indexed by a traverses the line from d(a) to its
own generic value, while all primal coordinates remain fixed. -/
def deformParameters (d : α → k) : ChartRing k α ι →+* Polynomial (ChartRing k α ι) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (Sum.elim (fun a => Polynomial.C (MvPolynomial.C (d a)) + Polynomial.X*
      Polynomial.C (MvPolynomial.X (.inl a)-MvPolynomial.C (d a)))
      (fun i => Polynomial.C (MvPolynomial.X (.inr i))))

omit [IsDomain k] in
theorem deform_at_one (d : α → k) :
    (Polynomial.evalRingHom 1).comp (deformParameters d (ι:=ι))=RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [deformParameters]
  · rintro (a|i) <;> simp [deformParameters]

omit [IsDomain k] in
theorem deform_at_zero (d : α → k) :
    (Polynomial.evalRingHom 0).comp (deformParameters d (ι:=ι))=center d := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [deformParameters,center]
  · rintro (a|i) <;> simp [deformParameters,center]

set_option maxHeartbeats 1500000 in
/-- Faithfulness before eliminating the linear-form constant. It suffices
that the reconstructed quadratic constants specialize to independent pure
squares after the free coefficient blocks are frozen. Arbitrary relations
are allowed to involve those free coefficients as well. -/
theorem chart_faithful (H : ι → ChartRing k α ι) (d : α → k)
    (diagonal : ∀i,center d (H i)=MvPolynomial.X (.inr i)^2) :
    Function.Injective (chartMap H) := by
  let B := ChartRing k α ι
  let D := deformParameters (ι:=ι) d
  let F := chartMap H
  let g := chartMap (fun i : ι => (MvPolynomial.X (.inr i) : B)^2)
  let liftCoeff : B →+* Polynomial B := MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (Sum.elim (fun a => Polynomial.C (MvPolynomial.X (.inl a))) (fun i => D (H i)))
  let lift := Polynomial.eval₂RingHom liftCoeff Polynomial.X
  have fiberCoeff : (Polynomial.evalRingHom 0).comp liftCoeff=g := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [liftCoeff,g,chartMap]
    · rintro (a|i)
      · simp [liftCoeff,g,chartMap]
      · simp only [RingHom.comp_apply,liftCoeff,MvPolynomial.eval₂Hom_X',Sum.elim_inr,g,chartMap]
        calc
          (Polynomial.evalRingHom 0) (D (H i)) = center d (H i) :=
            RingHom.congr_fun (deform_at_zero (ι:=ι) d) (H i)
          _ = _ := diagonal i
  have fiber : (Polynomial.evalRingHom 0).comp lift=g.comp (Polynomial.evalRingHom 0) := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa [lift] using RingHom.congr_fun fiberCoeff a
    · simp [lift]
  have hlift : Function.Injective lift :=
    injective_polynomial_lift lift g square_chart_injective (by simp [lift]) (fun p => by
      simp only [Polynomial.coeff_zero_eq_eval_zero]
      exact RingHom.congr_fun fiber p)
  have liftC (v : B) : lift (Polynomial.C v)=liftCoeff v := Polynomial.eval₂_C _ _
  have liftX : lift Polynomial.X=Polynomial.X := Polynomial.eval₂_X _ _
  have lc (a : k) : liftCoeff (MvPolynomial.C a)=Polynomial.C (MvPolynomial.C a) :=
    MvPolynomial.eval₂Hom_C _ _ _
  have lfree (a : α) : liftCoeff (MvPolynomial.X (.inl a))=Polynomial.C (MvPolynomial.X (.inl a)) :=
    MvPolynomial.eval₂Hom_X' _ _ _
  have lstate (i : ι) : liftCoeff (MvPolynomial.X (.inr i))=D (H i) :=
    MvPolynomial.eval₂Hom_X' _ _ _
  have square : lift.comp D=D.comp F := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply,D,F,chartMap,deformParameters,MvPolynomial.eval₂Hom_C,liftC,lc]
    · rintro (a|i)
      · simp only [RingHom.comp_apply,D,F,chartMap,deformParameters,MvPolynomial.eval₂Hom_X',
          Sum.elim_inl,map_add,map_mul,map_sub,liftC,liftX,lc,lfree]
      · simp only [RingHom.comp_apply,D,F,chartMap,deformParameters,MvPolynomial.eval₂Hom_X',
          Sum.elim_inr,liftC,lstate]
  intro p q eq
  have heq : lift (D p)=lift (D q) :=
    (RingHom.congr_fun square p).trans ((congrArg D eq).trans (RingHom.congr_fun square q).symm)
  have hd := congrArg (Polynomial.evalRingHom 1) (hlift heq)
  exact (RingHom.congr_fun (deform_at_one d) p).symm.trans (hd.trans (RingHom.congr_fun (deform_at_one d) q))

end
end PlanarUnitDistances.UniversalIncidence
