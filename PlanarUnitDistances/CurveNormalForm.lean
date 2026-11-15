import PlanarUnitDistances.CurveReflection

/-! An irreducible curve of bidegree (1,1) is a nonhorizontal affine line
or a translated, nondegenerate rectangular hyperbola in the z,w chart. -/

noncomputable section

namespace PlanarUnitDistances.CurveNormalForm

open MvPolynomial

variable {k : Type*} [Field k]
abbrev Poly (k : Type*) [Field k] := MvPolynomial (Fin 2) k

/-- Expand the actual bivariate polynomial, using both separate degree bounds. -/
theorem bilinear_expansion (f : Poly k) (hz : f.degreeOf 0 ≤ 1) (hw : f.degreeOf 1 ≤ 1) :
    ∃ a c d e : k, f = C a*X 0*X 1 + C c*X 0 + C d*X 1 + C e := by
  classical
  let z := Finsupp.single (0 : Fin 2) 1
  let w := Finsupp.single (1 : Fin 2) 1
  have hzw : (z: Fin 2 →₀ ℕ) ≠ w := by intro h; have := congr($(h) 0); simp [z,w] at this
  have hz₀ : (z: Fin 2 →₀ ℕ) ≠ 0 := by simp [z]
  have hw₀ : (w: Fin 2 →₀ ℕ) ≠ 0 := by simp [w]
  have hzw₀ : z+w ≠ 0 := by simp [hz₀,hw₀]
  have hzwz : z+w ≠ z := by simp [hw₀]
  have hzww : z+w ≠ w := by simp [hz₀]
  refine ⟨f.coeff (z+w), f.coeff z, f.coeff w, f.coeff 0, ?_⟩
  have hexpand (b : k) :
      (C b*X 0*X 1 : Poly k) = monomial (z+w) b := by
    rw [C_mul_X_eq_monomial]
    simpa [z,w] using (monomial_add_single (s := z) (a := b) (n := 1) (e := 1)).symm
  rw [hexpand,C_mul_X_eq_monomial,C_mul_X_eq_monomial]
  change f = monomial (z+w) _ + monomial z _ + monomial w _ + C _
  ext m
  by_cases ha : m=z+w
  · subst m; simp [hzwz.symm,hzww.symm,Ne.symm hzw₀]
  by_cases hb : m=z
  · subst m; simp [hzwz,hzw.symm,Ne.symm hz₀]
  by_cases hc : m=w
  · subst m; simp [hzww,hzw,Ne.symm hw₀]
  by_cases hd : m=0
  · subst m; simp [hzw₀,hz₀,hw₀]
  simp [Ne.symm ha,Ne.symm hb,Ne.symm hc,Ne.symm hd]
  by_contra hcoeff
  have hmem := mem_support_iff.mpr hcoeff
  have h₀ := (le_degreeOf_of_mem_support 0 hmem).trans hz
  have h₁ := (le_degreeOf_of_mem_support 1 hmem).trans hw
  rcases (show m 0 = 0 ∨ m 0 = 1 by omega) with h₀ | h₀ <;>
    rcases (show m 1 = 0 ∨ m 1 = 1 by omega) with h₁ | h₁
  · apply hd; ext j; fin_cases j <;> simp [h₀,h₁]
  · apply hc; ext j; fin_cases j <;> simp [w,h₀,h₁]
  · apply hb; ext j; fin_cases j <;> simp [z,h₀,h₁]
  · apply ha; ext j; fin_cases j <;> simp [z,w,h₀,h₁]

private theorem linear_factor_not_unit (i : Fin 2) (c : k) :
    ¬ IsUnit (X i - C c : Poly k) := by
  intro h
  have hz := h.map (eval (fun _ : Fin 2 ↦ c))
  simp at hz

/-- The parameters are explicit elements of the original coefficient field.
The branch with zero translated parameter would make both linear factors
nonunits, contradicting irreducibility. -/
theorem classify_bidegree_one (f : Poly k) (hf : Irreducible f)
    (hz : f.degreeOf 0 = 1) (hw : f.degreeOf 1 = 1) :
    (∃ e e' : k, e ≠ 0 ∧ ∀ z w : k, eval ![z,w] f = 0 ↔ w = e*z + e') ∨
    (∃ u v b : k, b ≠ 0 ∧ ∀ z w : k, eval ![z,w] f = 0 ↔ (z-u)*(w-v) = b) := by
  obtain ⟨a,c,d,e,hexp⟩ := bilinear_expansion f hz.le hw.le
  have heval (z w : k) : eval ![z,w] f = a*z*w + c*z + d*w + e := by
    rw [hexp]; simp
  by_cases ha : a = 0
  · left
    subst a
    have hnon (j l : Fin 2) (hb : j ≠ l) (b e : k) :
        (C b*X l+C e : Poly k).degreeOf j = 0 := by
      apply Nat.eq_zero_of_le_zero ((degreeOf_add_le _ _ _).trans ?_)
      have hdg := degreeOf_C_mul_le (X l : Poly k) j b
      simpa [degreeOf_X, hb, Ne.symm hb] using hdg
    have hc : c ≠ 0 := by
      rintro rfl
      simp [hexp,hnon 0 1 (by decide)] at hz
    have hd : d ≠ 0 := by
      rintro rfl
      simp [hexp,hnon 1 0 (by decide)] at hw
    refine ⟨-c/d,-e/d,div_ne_zero (neg_ne_zero.mpr hc) hd,?_⟩
    intro z w
    rw [heval]
    field_simp
    constructor <;> intro h <;> linear_combination h
  · right
    let u := -d/a
    let v := -c/a
    let b := (c*d-a*e)/a^2
    have hfac : f = C a * ((X 0-C u)*(X 1-C v)-C b) := by
      rw [hexp]
      have hu : a*u = -d := by dsimp [u]; field_simp
      have hv : a*v = -c := by dsimp [v]; field_simp
      have he : a*(u*v-b) = e := by dsimp [u,v,b]; field_simp; ring
      have hU := congrArg (C (σ := Fin 2)) hu
      have hV := congrArg (C (σ := Fin 2)) hv
      have hE := congrArg (C (σ := Fin 2)) he
      simp only [map_mul,map_neg,map_sub] at hU hV hE
      linear_combination (X 1)*hU + (X 0)*hV - hE
    have hb : b ≠ 0 := by
      intro h
      rw [h,map_zero,sub_zero,←mul_assoc] at hfac
      rcases hf.isUnit_or_isUnit hfac with hunit | hunit
      · exact linear_factor_not_unit 0 u (isUnit_of_mul_isUnit_right hunit)
      · exact linear_factor_not_unit 1 v hunit
    refine ⟨u,v,b,hb,fun z w ↦ ?_⟩
    simp [hfac,ha,sub_eq_zero]

open OAI.PlanarUnitDistances
open scoped ComplexConjugate


end PlanarUnitDistances.CurveNormalForm
