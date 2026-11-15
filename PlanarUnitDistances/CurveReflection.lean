import PlanarUnitDistances.PlaneBezout
import PlanarUnitDistances.GeometricCodegree

/-! The complex plane curve containing more than D² real points is invariant
under the involution (z,w) ↦ (conj w, conj z) of null coordinates. -/

noncomputable section

namespace PlanarUnitDistances.CurveReflection

open MvPolynomial
open OAI.PlanarUnitDistances
open scoped ComplexConjugate

abbrev Poly := MvPolynomial (Fin 2) ℂ
abbrev Point := Fin 2 → ℂ
private abbrev flip := Equiv.swap (0 : Fin 2) 1

def reflect : Poly ≃+* Poly :=
  (mapEquiv (Fin 2) Complex.conjAe.toRingEquiv).trans (renameEquiv ℂ flip).toRingEquiv

def reflectPoint (x : Point) : Point := fun j ↦ conj (x (flip j))

def realPoint : Plane ↪ Point :=
  ⟨fun p ↦ ![zCoord p,conj (zCoord p)], fun _ _ h ↦ zCoord_injective (congrFun h 0)⟩

theorem realPoint_fixed (p : Plane) : reflectPoint (realPoint p) = realPoint p := by
  funext j
  fin_cases j
  · change conj (conj (zCoord p)) = zCoord p
    simp
  · rfl

theorem reflect_eval (x : Point) (f : Poly) :
    eval (reflectPoint x) (reflect f) = conj (eval x f) := by
  change eval (reflectPoint x) (rename flip (map Complex.conjAe.toRingHom f)) = _
  rw [eval_rename, map_eval]
  have h : reflectPoint x ∘ flip = conj ∘ x := by
    funext j
    simp [reflectPoint, flip]
  rw [h]
  rfl

theorem reflect_degree (f : Poly) : (reflect f).totalDegree = f.totalDegree := by
  change ((renameEquiv ℂ flip) (map Complex.conjAe.toRingHom f)).totalDegree = _
  rw [totalDegree_renameEquiv]
  exact congrArg (fun S : Finset (Fin 2 →₀ ℕ) ↦ S.sup fun m ↦ m.sum fun _ n ↦ n)
    (support_map_of_injective f Complex.conjAe.injective)

theorem reflect_degreeOf (i : Fin 2) (f : Poly) :
    (reflect f).degreeOf (flip i) = f.degreeOf i := by
  change (rename flip (map Complex.conjAe.toRingHom f)).degreeOf (flip i) = _
  rw [degreeOf_rename_of_injective flip.injective, degreeOf_def, degreeOf_def]
  exact congrArg (Multiset.count i) (degrees_map_of_injective f (f := Complex.conjAe.toRingHom)
    Complex.conjAe.injective)

/-- The degree-D threshold forces divisibility in the polynomial ring itself,
and hence association because reflection preserves irreducibility. -/
theorem rich_curve_associated (f : Poly) (hf : Irreducible f) {D : ℕ} (hd : f.totalDegree ≤ D)
    (S : Finset Plane) (hS : D^2 < S.card) (hz : ∀ p ∈ S, eval (realPoint p) f = 0) :
    f ∣ reflect f ∧ Associated f (reflect f) := by
  have hdvd : f ∣ reflect f := by
    by_contra hn
    have h := PlaneBezout.common_zeros f (reflect f) hf hn (S.map realPoint)
      (by rintro x hx; obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hx; exact hz p hp)
      (by rintro x hx; obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hx
          rw [← realPoint_fixed p, reflect_eval, hz p hp, map_zero])
    rw [Finset.card_map, reflect_degree] at h
    exact (not_lt_of_ge ((h.trans (Nat.mul_le_mul hd hd)).trans_eq (pow_two D).symm)) hS
  exact ⟨hdvd, hf.associated_of_dvd ((MulEquiv.irreducible_iff reflect).mpr hf) hdvd⟩

/-- Invariance up to a nonzero constant factor, and invariance of the entire
complex zero set, with equality of the separate z and w degrees. -/
theorem rich_curve_symmetry (f : Poly) (hf : Irreducible f) {D : ℕ} (hd : f.totalDegree ≤ D)
    (S : Finset Plane) (hS : D^2 < S.card) (hz : ∀ p ∈ S, eval (realPoint p) f = 0) :
    (∃ c : ℂ, c ≠ 0 ∧ reflect f = C c * f) ∧
      (∀ x : Point, eval (reflectPoint x) f = 0 ↔ eval x f = 0) ∧ f.degreeOf 0 = f.degreeOf 1 := by
  obtain ⟨u,hu⟩ := (rich_curve_associated f hf hd S hS hz).2
  obtain ⟨c,hc,he⟩ := isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  have hfactor : reflect f = C c * f := by rw [← hu, he, mul_comm]
  have hcn : c ≠ 0 := hc.ne_zero
  refine ⟨⟨c,hcn,hfactor⟩, ?_, ?_⟩
  · intro x
    have hh := reflect_eval x f
    rw [hfactor, map_mul, eval_C] at hh
    constructor
    · intro h
      rw [h,mul_zero] at hh
      exact star_eq_zero.mp hh.symm
    · intro h
      rw [h,map_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_left hcn
  · have hdeg := reflect_degreeOf 0 f
    rw [hfactor, degreeOf_C_mul _ _ (mem_nonZeroDivisors_of_ne_zero hcn)] at hdeg
    simpa [flip] using hdeg.symm

/-- Two distinct real-plane points always have different z coordinates and
different w coordinates. Hence both coordinate projections on the *whole*
curve are nonconstant, witnessed by the same two real points. -/
theorem rich_curve_nonconstant_projections (f : Poly) (hf : Irreducible f) {D : ℕ} (hd : f.totalDegree ≤ D)
    (S : Finset Plane) (hS : D^2 < S.card) (hz : ∀ p ∈ S, eval (realPoint p) f = 0) :
    ∃ p ∈ S, ∃ q ∈ S, eval (realPoint p) f = 0 ∧ eval (realPoint q) f = 0 ∧
      ∀ j : Fin 2, realPoint p j ≠ realPoint q j := by
  have hpos : 0 < f.totalDegree := by
    by_contra! h
    have he := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h)
    have hcoeff : f.coeff 0 ≠ 0 := fun hc ↦ hf.ne_zero (by simpa [hc] using he)
    exact hf.not_isUnit (isUnit_iff_eq_C_of_isReduced.mpr ⟨_, isUnit_iff_ne_zero.mpr hcoeff, he⟩)
  have hone : 1 ≤ D^2 := Nat.one_le_pow _ _ (hpos.trans_le hd)
  obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp (hone.trans_lt hS)
  refine ⟨p,hp,q,hq,hz p hp,hz q hq,?_⟩
  intro j
  fin_cases j
  · exact zCoord_injective.ne hpq
  · exact Complex.conjAe.injective.ne (zCoord_injective.ne hpq)

/-- A reflection-symmetric translated hyperbola has
conjugate centers and real parameter. The normalized mixed coefficient removes
the scalar ambiguity in the equation. -/
theorem hyperbola_center (u v b : ℂ)
    (hsym : ∀ z w : ℂ, (z-u)*(w-v)=b → (conj w-u)*(conj z-v)=b) :
    v = conj u ∧ conj b = b := by
  have he (t : ℂ) (ht : t ≠ 0) :=
    hsym (u+t) (v+b/t) (by field_simp; ring)
  have hx (t : ℝ) (ht : t ≠ 0) :
      (conj v-u) * (t : ℂ)^2 +
        ((conj v-u)*(conj u-v) + conj b - b) * t + conj b * (conj u-v) = 0 := by
    have h := he (t:ℂ) (by exact_mod_cast ht)
    simp only [map_add, map_div₀, Complex.conj_ofReal] at h
    field_simp [Complex.ofReal_ne_zero.mpr ht] at h
    linear_combination h
  have h₁ := hx 1 (by norm_num)
  have h₂ := hx 2 (by norm_num)
  have h₃ := hx 3 (by norm_num)
  norm_num only [Complex.ofReal_one, Complex.ofReal_ofNat] at h₁ h₂ h₃
  have hcenter : conj v - u = 0 := by linear_combination (h₃ - 2*h₂ + h₁)/2
  have hv : v = conj u := by
    simpa using congrArg conj (sub_eq_zero.mp hcenter)
  exact ⟨hv,by rw [hcenter, ← hv] at h₁; simpa [sub_eq_zero] using h₁⟩

/-- In the exceptional case β=1 the original real points describe the usual
Euclidean unit circle, including its radius and its center. -/
theorem hyperbola_one_is_unit_circle (u v : ℂ)
    (hsym : ∀ z w : ℂ, (z-u)*(w-v)=1 → (conj w-u)*(conj z-v)=1) :
    ∃ center : Plane, zCoord center = u ∧ ∀ p : Plane,
      (zCoord p-u)*(conj (zCoord p)-v)=1 ↔ dist p center = 1 := by
  have hv := (hyperbola_center u v 1 hsym).1
  let center := WithLp.toLp 2 ![u.re,u.im]
  have hc : zCoord center = u := by apply Complex.ext <;> rfl
  refine ⟨center,hc,fun p ↦ ?_⟩
  rw [hv, ← hc, ← map_sub, Complex.mul_conj, zCoord_sub_normSq]
  constructor
  · intro h
    have h' : dist p center ^ 2 = 1 := by exact_mod_cast h
    nlinarith [dist_nonneg (x := p) (y := center)]
  · intro h
    simp [h]

end PlanarUnitDistances.CurveReflection
