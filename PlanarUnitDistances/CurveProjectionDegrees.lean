import PlanarUnitDistances.BivariateCurveCoordinates

namespace PlanarUnitDistances.BivariateCurveCoordinates
open Polynomial

private theorem first_coordinate_constant {k : Type*} [Field k] (f : k[X][X])
    (irr : Irreducible f) (deg : f.natDegree=0) {a b c d : k}
    (r : f.aevalAeval a b=0) (s : f.aevalAeval c d=0) : c=a := by
  let p := f.coeff 0
  have fp : f=C p := Polynomial.eq_C_of_natDegree_eq_zero deg
  have prime : Irreducible p := by
    refine ⟨fun h ↦ irr.not_isUnit (fp ▸ h.map C),?_⟩
    intro u v fac
    have h := irr.isUnit_or_isUnit (show f=C u*C v by rw [fp,fac,map_mul])
    exact h.imp (fun h ↦ by simpa using h.map (evalRingHom (0:k[X])))
      (fun h ↦ by simpa using h.map (evalRingHom (0:k[X])))
  have ha : p.eval a=0 := by simpa [fp] using r
  have hc : p.eval c=0 := by simpa [fp] using s
  have dv : X-C a ∣ p := Polynomial.dvd_iff_isRoot.mpr ha
  obtain ⟨q,eq⟩ := (Polynomial.irreducible_X_sub_C a).dvd_symm prime dv
  have h := congrArg (fun t : k[X] ↦ t.eval c) eq
  simpa [hc,sub_eq_zero] using h

/-- On an irreducible plane curve whose two projections are nonconstant,
the two polynomial partial degrees are both positive. Only two distinct
coordinate values per projection are needed. -/
theorem degrees_of_projections {k : Type*} [Field k] (f : MvPolynomial (Fin 2) k) (irr : Irreducible f)
    (proj : ∀ j : Fin 2,∃ p q : Fin 2 → k, MvPolynomial.eval p f=0 ∧
      MvPolynomial.eval q f=0 ∧ p j≠q j) : f.degreeOf 0≠0 ∧ f.degreeOf 1≠0 := by
  have enc := (MulEquiv.irreducible_iff (encode k)).mpr irr
  have van (p : Fin 2 → k) (h : MvPolynomial.eval p f=0) : (encode k f).aevalAeval (p 0) (p 1)=0 := by
    rw [OAI.PlanarUnitDistances.GenericNoncoincidence.aevalAeval_eq_eval₂,encode_eval]
    have e : ![p 0,p 1]=p := by funext i; fin_cases i <;> rfl
    simpa [e,MvPolynomial.aeval_def] using h
  constructor
  · intro dz
    obtain ⟨p,q,hp,hq,hpq⟩ := proj 1
    apply hpq
    apply first_coordinate_constant (Bivariate.swap (encode k f))
      ((MulEquiv.irreducible_iff Bivariate.swap).mpr enc) ((horizontal_degree _).trans dz)
    · rw [Bivariate.aevalAeval_swap]; exact van q hq
    · rw [Bivariate.aevalAeval_swap]; exact van p hp
  · intro dw
    obtain ⟨p,q,hp,hq,hpq⟩ := proj 0
    exact hpq (first_coordinate_constant (encode k f) enc ((vertical_degree _).trans dw) (van q hq) (van p hp))

end PlanarUnitDistances.BivariateCurveCoordinates
