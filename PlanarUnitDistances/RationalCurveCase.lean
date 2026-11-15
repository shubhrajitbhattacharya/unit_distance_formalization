import PlanarUnitDistances.CurveNormalForm
import PlanarUnitDistances.InfiniteAbscissas

namespace PlanarUnitDistances.RationalCurveCase
open MvPolynomial Competition CurveReflection
open scoped ComplexConjugate
noncomputable section

private theorem divides_of_zero_set {f h : Poly₂} (irr : Irreducible f)
    (van : ∀ x : Fin 2 → ℂ,eval x f=0 → eval x h=0) : f∣h := by
  let J := Ideal.span ({f} : Set Poly₂)
  let _ : J.IsPrime := (Ideal.span_singleton_prime irr.ne_zero).mpr irr.prime
  have hh : h∈vanishingIdeal ℂ (zeroLocus ℂ J) :=
    fun x hx => van x (hx f (Ideal.subset_span (Set.mem_singleton _)))
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) J] at hh
  exact Ideal.mem_span_singleton.mp hh

theorem degree_symmetry {f : Poly₂} (irr : Irreducible f)
    (symm : ∀ z w : ℂ,eval ![z,w] f=0 ↔ eval ![conj w,conj z] f=0) :
    f.degreeOf 0=f.degreeOf 1 := by
  have eta (x : Fin 2 → ℂ) : ![x 0,x 1]=x := by funext d; fin_cases d <;> rfl
  have rr (x : Fin 2 → ℂ) : reflectPoint (reflectPoint x)=x := by
    funext i; fin_cases i <;> simp [reflectPoint]
  have re (x : Fin 2 → ℂ) : reflectPoint x=![conj (x 1),conj (x 0)] := by
    funext i; fin_cases i <;> rfl
  have dv : f∣reflect f := divides_of_zero_set irr (fun x h => by
    have v := (symm (x 0) (x 1)).mp (by rwa [eta])
    have ev := reflect_eval (reflectPoint x) f
    rwa [rr,re,v,map_zero] at ev)
  obtain ⟨u,hu⟩ := irr.associated_of_dvd ((MulEquiv.irreducible_iff reflect).mpr irr) dv
  obtain ⟨c,hc,ce⟩ := isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  have fac : reflect f=C c*f := by rw [←hu,ce,mul_comm]
  have deg := reflect_degreeOf 0 f
  rw [fac,degreeOf_C_mul _ _ (mem_nonZeroDivisors_of_ne_zero hc.ne_zero)] at deg
  exact deg.symm

def lineEq (e c : ℂ) : Poly₂ := X 1-(C e*X 0+C c)
def hyperEq (u v b : ℂ) : Poly₂ := (X 0-C u)*(X 1-C v)-C b

/-- The classification holds as polynomial divisibility, so it applies to
the generic positions over every extension. It uses only the actual curve
pair hypotheses and excludes the unit circle only when both curves are it. -/
theorem classify {f g : Poly₂} (pair : CurvePair f g) (same : g∣f) (one : f.degreeOf 1=1) :
    (∃ e c : ℂ,e≠0 ∧ f∣lineEq e c ∧ g∣lineEq e c) ∨
    (∃ u v b : ℂ,b≠0 ∧ b≠1 ∧ f∣hyperEq u v b ∧ g∣hyperEq u v b) := by
  obtain ⟨hf,symf,_⟩ := pair.1 f (Or.inl rfl)
  have hg := (pair.1 g (Or.inr rfl)).1
  have eta (x : Fin 2 → ℂ) : ![x 0,x 1]=x := by funext d; fin_cases d <;> rfl
  rcases CurveNormalForm.classify_bidegree_one f hf ((degree_symmetry hf symf).trans one) one with
    ⟨e,c,ne,eq⟩|⟨u,v,b,ne,eq⟩
  · have dv : f∣lineEq e c := divides_of_zero_set hf (fun x hx => by
      have h := (eq (x 0) (x 1)).mp (by rwa [eta])
      simpa only [lineEq,map_sub,map_add,map_mul,eval_X,eval_C,sub_eq_zero] using h)
    exact Or.inl ⟨e,c,ne,dv,same.trans dv⟩
  · have sym (z w : ℂ) (h : (z-u)*(w-v)=b) : (conj w-u)*(conj z-v)=b :=
      (eq _ _).mp ((symf _ _).mp ((eq _ _).mpr h))
    have hv := (hyperbola_center u v b sym).1
    have no : b≠1 := by
      rintro rfl
      apply pair.2
      refine ⟨u,fun x => ?_⟩
      have h := eq (x 0) (x 1)
      rw [eta,hv] at h
      have associated := hg.associated_of_dvd hf same
      have zeros : eval x g=0 ↔ eval x f=0 := by
        constructor
        · rintro hx; obtain ⟨d,hd⟩ := same; simp [hd,hx]
        · rintro hx; obtain ⟨d,hd⟩ := associated.symm.dvd; simp [hd,hx]
      exact ⟨h,zeros.trans h⟩
    have dv : f∣hyperEq u v b := divides_of_zero_set hf (fun x hx => by
      have h := (eq (x 0) (x 1)).mp (by rwa [eta])
      simpa only [hyperEq,map_sub,map_mul,eval_X,eval_C,sub_eq_zero] using h)
    exact Or.inr ⟨u,v,b,ne,no,dv,same.trans dv⟩

end
end PlanarUnitDistances.RationalCurveCase
