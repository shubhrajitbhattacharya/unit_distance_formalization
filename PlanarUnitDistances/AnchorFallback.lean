import Mathlib
import PlanarUnitDistances.QuadraticRadicals

namespace PlanarUnitDistances.AnchorFallback
open Matrix MvPolynomial OAI.PlanarUnitDistances.Radicals
open scoped Classical
noncomputable section

variable {R : Type*} [CommRing R]

/-- Signed cofactors of the radical column in the first three equations. -/
def cof (x y : Fin 4 → R) : Fin 3 → R :=
  ![x 1*y 2-x 2*y 1,x 2*y 0-x 0*y 2,x 0*y 1-x 1*y 0]

def aug (x y b a s : Fin 4 → R) : Matrix (Fin 4) (Fin 4) R :=
  fun i => ![x i,y i,-s i,b i-s i*a i]

def flip (s : Fin 4 → R) (i : Fin 4) := if i=3 then -s i else s i

/-- Cramer's numerator minus a₄ times the coefficient determinant. -/
def residual (x y b a s : Fin 4 → R) :=
  ∑ i : Fin 3,cof x y i*(b i.castSucc+s i.castSucc*(a 3-a i.castSucc))

/-- Flipping only the fourth radical isolates the cofactor identity without
dividing by the first-three determinant. -/
theorem det_flip (x y b a s : Fin 4 → R) :
    (aug x y b a s).det - (aug x y b a (flip s)).det =
      2*s 3*residual x y b a s := by
  have a0 (s' : Fin 4 → R) (i) : aug x y b a s' i 0=x i := rfl
  have a1 (s' : Fin 4 → R) (i) : aug x y b a s' i 1=y i := rfl
  have a2 (s' : Fin 4 → R) (i) : aug x y b a s' i 2= -s' i := rfl
  have a3 (s' : Fin 4 → R) (i) : aug x y b a s' i 3=b i-s' i*a i := rfl
  rw [Matrix.det_succ_row _ 3, Matrix.det_succ_row (aug x y b a (flip s)) 3]
  simp only [Fin.sum_univ_four,Matrix.det_fin_three,Matrix.submatrix_apply,
    show (0:Fin 4).succAbove (0:Fin 3) = 1 from rfl,
    show (0:Fin 4).succAbove (1:Fin 3) = 2 from rfl,
    show (0:Fin 4).succAbove (2:Fin 3) = 3 from rfl,
    show (1:Fin 4).succAbove (0:Fin 3) = 0 from rfl,
    show (1:Fin 4).succAbove (1:Fin 3) = 2 from rfl,
    show (1:Fin 4).succAbove (2:Fin 3) = 3 from rfl,
    show (2:Fin 4).succAbove (0:Fin 3) = 0 from rfl,
    show (2:Fin 4).succAbove (1:Fin 3) = 1 from rfl,
    show (2:Fin 4).succAbove (2:Fin 3) = 3 from rfl,
    show (3:Fin 4).succAbove (0:Fin 3) = 0 from rfl,
    show (3:Fin 4).succAbove (1:Fin 3) = 1 from rfl,
    show (3:Fin 4).succAbove (2:Fin 3) = 2 from rfl]
  simp only [a0,a1,a2,a3]
  norm_num [flip,residual,cof,Fin.sum_univ_three,show (0:Fin 4)≠3 by decide,
    show (1:Fin 4)≠3 by decide,show (2:Fin 4)≠3 by decide,
    show (0:Fin 3).castSucc=0 from rfl,show (1:Fin 3).castSucc=1 from rfl,
    show (2:Fin 3).castSucc=2 from rfl,Matrix.cons_val_two,Matrix.cons_val_fin_one]
  ring

/-- At any solution residual = (a₄−A) times the signed linear radical sum.
This identity holds at a singular first-three matrix as well. -/
theorem residual_at_solution (x y b a s : Fin 4 → R) (h k A : R)
    (eqs : ∀ i,x i*h+y i*k-s i*A = b i-s i*a i) :
    residual x y b a s = (a 3-A) * ∑ i : Fin 3,cof x y i*s i.castSucc := by
  have hb (i : Fin 4) : b i = x i*h+y i*k+s i*(a i-A) := by linear_combination -(eqs i)
  simp [residual,cof,Fin.sum_univ_three,hb]
  ring

/-- A degree-four relation for a sum of three radicals; eliminating all eight
signs would instead produce the square of this expression. -/
def eliminate3 (u v w : R) := (w-u-v)^2-4*u*v

theorem eliminate3_factors (x y z : R) :
    eliminate3 (x^2) (y^2) (z^2) = (z-x-y)*(z+x+y)*(z-x+y)*(z+x-y) := by
  unfold eliminate3
  ring

def fallback (c : Fin 3 → R) (D : Fin 4 → R) :=
  eliminate3 ((c 0)^2*D 0) ((c 1)^2*D 1) ((c 2)^2*D 2)

/-- The explicit eliminant specializes to zero even if some specialized
radicals or some position minors vanish. -/
theorem fallback_vanishes {L : Type*} [CommRing L] (f : R →+* L) (c : Fin 3 → R)
    (D : Fin 4 → R) (s : Fin 4 → L) (hs : ∀ i,s i^2=f (D i))
    (hlinear : ∑ i : Fin 3,f (c i)*s i.castSucc=0) : f (fallback c D)=0 := by
  simp only [Fin.sum_univ_three] at hlinear
  change f (c 0)*s 0+f (c 1)*s 1+f (c 2)*s 2=0 at hlinear
  have hfac := eliminate3_factors (f (c 0)*s 0) (f (c 1)*s 1) (f (c 2)*s 2)
  rw [show f (c 2)*s 2+f (c 0)*s 0+f (c 1)*s 1=0 by linear_combination hlinear] at hfac
  simpa [fallback,eliminate3,mul_pow,hs,show f 4=4 from map_ofNat f 4] using hfac

theorem fallback_degree {k σ : Type*} [Field k] (c : Fin 3 → MvPolynomial σ k)
    (D : Fin 4 → MvPolynomial σ k) (hc : ∀ i,(c i).totalDegree ≤ 1)
    (hD : ∀ i,(D i).totalDegree ≤ 4) : (fallback c D).totalDegree ≤ 12 := by
  let U (i : Fin 3) := (c i)^2 * D i.castSucc
  have ub (i : Fin 3) : (U i).totalDegree ≤ 6 := by
    dsimp [U]
    apply (totalDegree_mul _ _).trans
    have hp := totalDegree_pow (c i) 2
    have := hc i
    have := hD i.castSucc
    omega
  change ((U 2-U 0-U 1)^2-4*(U 0)*(U 1)).totalDegree ≤ 12
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply (totalDegree_pow _ 2).trans
    have hs := totalDegree_sub (U 2) (U 0)
    have ht := totalDegree_sub (U 2-U 0) (U 1)
    have := ub 0; have := ub 1; have := ub 2
    omega
  · have h4 : (4: MvPolynomial σ k).totalDegree = 0 := by
      rw [show (4:MvPolynomial σ k) = C (4:k) from (map_ofNat C 4).symm]; exact totalDegree_C _
    have h1 := totalDegree_mul (4:MvPolynomial σ k) (U 0)
    have h2 := totalDegree_mul (4*U 0) (U 1)
    have := ub 0; have := ub 1
    omega

section Generic
universe u
variable {K : Type u} [Field K] [CharZero K] {D : Fin 4 → K}
abbrev Model (D : Fin 4 → K) := RadicalModel [D 0,D 1,D 2,D 3]

omit [CharZero K] in
private theorem affine_independent (m : Model D) (hD : SquareIndependent [D 0,D 1,D 2,D 3])
    (c : Fin 4 → K) (b : K) (h : m.incl b+∑ i,m.incl (c i)*m.roots i=0) :
    b=0 ∧ ∀ i,c i=0 := by
  have coeff (i : Fin 4) : c i=0 := by
    have hflip := congrArg (m.flips i) h
    simp only [map_zero,map_add,map_sum,map_mul,m.flips_base,m.flips_roots] at hflip
    have hd : ∑ j : Fin 4, (m.incl (c j)*m.roots j -
        m.incl (c j)*(if i=j then -m.roots j else m.roots j)) =
        2*(m.incl (c i)*m.roots i) := by
      calc
        _ = ∑ j : Fin 4,if i=j then 2*(m.incl (c i)*m.roots i) else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hij : i=j
          · subst j; simp; ring
          · simp [hij]
        _ = _ := by simp
    rw [Finset.sum_sub_distrib] at hd
    have hz : 2*(m.incl (c i)*m.roots i)=0 := by linear_combination h - hflip - hd
    exact m.incl.injective (by simpa only [map_zero] using
      ((mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left two_ne_zero)).resolve_right (m.root_ne_zero hD i)))
  refine ⟨m.incl.injective ?_,coeff⟩
  simpa [coeff] using h

private theorem mapped_cof {T : Type*} [CommRing T] (f : R →+* T) (x y : Fin 4 → R)
    (i : Fin 3) : cof (f ∘ x) (f ∘ y) i = f (cof x y i) := by
  fin_cases i <;> simp [cof]

/-- If the generic augmented determinant vanishes, the regular polynomial
coefficients in its Cramer relation vanish individually. This statement
descends from the generic field before specializing any coordinate. -/
theorem generic_coefficients (f : R →+* K) (hf : Function.Injective f) (m : Model D)
    (hD : SquareIndependent [D 0,D 1,D 2,D 3]) (x y b a : Fin 4 → R)
    (gen : (aug ((m.incl.comp f) ∘ x) ((m.incl.comp f) ∘ y)
      ((m.incl.comp f) ∘ b) ((m.incl.comp f) ∘ a) m.roots).det = 0) :
    (∑ i : Fin 3,cof x y i*b i.castSucc)=0 ∧
      ∀ i : Fin 3,cof x y i*(a 3-a i.castSucc)=0 := by
  let v := m.incl.comp f
  let X := v ∘ x
  let Y := v ∘ y
  let B := v ∘ b
  let A := v ∘ a
  have hflip := congrArg (m.flips 3) gen
  have zflip : (aug X Y B A (flip m.roots)).det=0 := by
    let ψ := (m.flips 3).toRingHom
    have mat : ψ.mapMatrix (aug X Y B A m.roots) = aug X Y B A (flip m.roots) := by
      ext i j
      change m.flips 3 (aug X Y B A m.roots i j) = _
      fin_cases j <;> simp [X,Y,B,A,v,aug,flip,m.flips_base,m.flips_roots,eq_comm]
    rw [←mat,←ψ.map_det,show (aug X Y B A m.roots).det=0 from gen,map_zero]
  have eq := det_flip X Y B A m.roots
  rw [show (aug X Y B A m.roots).det=0 from gen,zflip,sub_self] at eq
  have resid := (mul_eq_zero.mp eq.symm).resolve_left (mul_ne_zero two_ne_zero (m.root_ne_zero hD 3))
  let C₀ := ∑ i : Fin 3,cof x y i*b i.castSucc
  let c (i : Fin 3) := cof x y i*(a 3-a i.castSucc)
  let coeff : Fin 4 → K := ![f (c 0),f (c 1),f (c 2),0]
  have id : m.incl (f C₀)+∑ i,m.incl (coeff i)*m.roots i = 0 := by
    apply Eq.trans _ resid
    simp only [residual,X,Y,B,A,C₀,v,mapped_cof,Function.comp_apply,RingHom.comp_apply,
      c,coeff,Fin.sum_univ_three,Fin.sum_univ_four,map_add,map_sub,map_mul]
    simp
    ring
  obtain ⟨base,coeffs⟩ := affine_independent m hD coeff (f C₀) id
  refine ⟨hf (base.trans (map_zero f).symm),?_⟩
  intro i
  apply hf
  fin_cases i <;> first | simpa [coeff,c] using coeffs 0 | simpa [coeff,c] using coeffs 1 |
    simpa [coeff,c] using coeffs 2

/-- The degree-four eliminant does not vanish generically: each signed
linear combination of the three independent radicals has a nonzero term. -/
theorem fallback_ne_zero (f : R →+* K) (hf : Function.Injective f) (D₀ : Fin 4 → R)
    (m : Model (f ∘ D₀)) (hD : SquareIndependent [f (D₀ 0),f (D₀ 1),f (D₀ 2),f (D₀ 3)])
    (c : Fin 3 → R) (cnz : ∃ i,c i≠0) : fallback c D₀ ≠ 0 := by
  let v := m.incl.comp f
  let x (i : Fin 3) := v (c i)*m.roots i.castSucc
  have linear (a b : ℕ) :
      x 2+(-1:m.Carrier)^a*x 0+(-1:m.Carrier)^b*x 1 ≠ 0 := by
    intro hz
    let cf : Fin 4 → K := ![(-1:K)^a*f (c 0),(-1:K)^b*f (c 1),f (c 2),0]
    have rel : ∑ i,m.incl (cf i)*m.roots i=0 := by
      simp [Fin.sum_univ_four,cf,x,v] at hz ⊢
      linear_combination hz
    have eq := m.linear_relation hD cf rel
    obtain ⟨i,hi⟩ := cnz
    have eq0 := eq 0; have eq1 := eq 1; have eq2 := eq 2
    simp [cf] at eq0 eq1 eq2
    apply hi
    fin_cases i <;> apply hf <;> first | simpa using eq0 | simpa using eq1 | simpa using eq2
  have e0 := linear 0 0
  have e1 := linear 1 1
  have e2 := linear 1 0
  have e3 := linear 0 1
  simp only [pow_zero,pow_one,one_mul,neg_one_mul,←sub_eq_add_neg] at e0 e1 e2 e3
  have ng := mul_ne_zero (mul_ne_zero (mul_ne_zero e1 e0) e2) e3
  rw [←eliminate3_factors] at ng
  intro h
  apply ng
  have sq (i : Fin 3) : (x i)^2=v ((c i)^2*D₀ i.castSucc) := by
    dsimp [x,v]
    rw [mul_pow,map_mul,map_pow,m.roots_sq]
    fin_cases i <;> simp
  simpa [eliminate3,fallback,sq,show v 4=4 from map_ofNat v 4] using congrArg v h

end Generic
/-- Specialization of the Cramer branch. An arbitrary algebraic specialization
of the coefficient ring is allowed; it may kill every minor. -/
theorem specialized_fallback {K : Type*} [Field K] [CharZero K] (f : R →+* K)
    (hf : Function.Injective f) (D : Fin 4 → R) (m : Model (f ∘ D))
    (hind : SquareIndependent [f (D 0),f (D 1),f (D 2),f (D 3)]) (x y b a : Fin 4 → R)
    (gen : (aug ((m.incl.comp f) ∘ x) ((m.incl.comp f) ∘ y)
      ((m.incl.comp f) ∘ b) ((m.incl.comp f) ∘ a) m.roots).det=0)
    {T : Type*} [Field T] (g : R →+* T) (s : Fin 4 → T) (h k A : T)
    (hs : ∀ i,s i^2=g (D i))
    (eqs : ∀ i,g (x i)*h+g (y i)*k-s i*A = g (b i)-s i*g (a i))
    (hne : A≠g (a 3)) : g (fallback (cof x y) D)=0 := by
  obtain ⟨h0,hc⟩ := generic_coefficients f hf m hind x y b a gen
  have hb := congrArg g h0
  simp only [map_sum,map_mul,map_zero] at hb
  have rel : residual (g ∘ x) (g ∘ y) (g ∘ b) (g ∘ a) s=0 := by
    unfold residual
    simp only [mapped_cof,Function.comp_apply,mul_add,Finset.sum_add_distrib,hb,zero_add]
    apply Finset.sum_eq_zero
    intro i _
    have hh := congrArg g (hc i)
    simp only [map_mul,map_sub,map_zero] at hh
    linear_combination s i.castSucc * hh
  have hf' := residual_at_solution (g ∘ x) (g ∘ y) (g ∘ b) (g ∘ a) s h k A eqs
  rw [rel] at hf'
  have linear := (mul_eq_zero.mp hf'.symm).resolve_left (sub_ne_zero.mpr hne.symm)
  apply fallback_vanishes g _ _ s hs
  simpa only [mapped_cof] using linear

section Position
variable {k : Type*} [Field k] [CharZero k]
abbrev PlanePoly (k : Type*) [Field k] := MvPolynomial (Fin 2) k

/-- The two position columns of the actual anchor matrix, including the
derivative factor two of the Cartesian distance polynomial. -/
def pos (j : Fin 2) (z : k) : PlanePoly k := 2*(X j-C z)

omit [CharZero k] in
private theorem pos_minor (r s p q : k) :
    pos 0 r * pos 1 q - pos 0 p * pos 1 s =
      C (4:k)*(C (s-q)*X 0+C (p-r)*X 1+C (r*q-p*s)) := by
  simp only [pos,map_sub,map_mul,map_ofNat]
  ring

omit [CharZero k] in
private theorem pos_minor_degree (r s p q : k) :
    (pos 0 r*pos 1 q-pos 0 p*pos 1 s).totalDegree ≤ 1 := by
  rw [pos_minor]
  apply (totalDegree_mul ..).trans
  rw [totalDegree_C,zero_add]
  apply (totalDegree_add ..).trans
  apply max_le _ (by rw [totalDegree_C]; omega)
  apply (totalDegree_add ..).trans
  apply max_le <;> apply (totalDegree_mul ..).trans <;> rw [totalDegree_C,totalDegree_X]

omit [CharZero k] in
theorem position_cofactor_degrees (r s : Fin 4 → k) (i : Fin 3) :
    (cof (fun j => pos 0 (r j)) (fun j => pos 1 (s j)) i).totalDegree ≤ 1 := by
  fin_cases i <;> apply pos_minor_degree

/-- The specific minor det(v₁,v₂) is a nonzero polynomial for distinct
anchors, including when the two positions have a common coordinate. -/
theorem position_cofactor_nonzero (r s : Fin 4 → k) (distinct : (r 0,s 0)≠(r 1,s 1)) :
    cof (fun j => pos 0 (r j)) (fun j => pos 1 (s j)) 2 ≠ 0 := by
  intro hz
  apply distinct
  change pos 0 (r 0)*pos 1 (s 1)-pos 0 (r 1)*pos 1 (s 0)=0 at hz
  have atPt (p q : k) := congrArg (MvPolynomial.eval ![p,q]) hz
  have h1 := atPt (r 0 + 1) (s 0)
  have h2 := atPt (r 0) (s 0 + 1)
  simp [pos] at h1 h2
  apply Prod.ext
  · exact sub_eq_zero.mp h2
  · exact sub_eq_zero.mp h1

/-- Complete zero-determinant branch for four Cartesian anchors over a
generic field carrying the independent roots. Its nonzero degree-twelve
polynomial works uniformly in every specialization and every solution. -/
theorem degree_twelve_branch {K : Type*} [Field K] [CharZero K]
    (r s : Fin 4 → k) (distinct : (r 0,s 0)≠(r 1,s 1))
    (b a D : Fin 4 → PlanePoly k) (hD : ∀ i,(D i).totalDegree ≤ 4)
    (f : PlanePoly k →+* K) (hf : Function.Injective f) (m : Model (f ∘ D))
    (hind : SquareIndependent [f (D 0),f (D 1),f (D 2),f (D 3)])
    (gen : (aug (fun j => m.incl (f (pos 0 (r j)))) (fun j => m.incl (f (pos 1 (s j))))
      ((m.incl.comp f) ∘ b) ((m.incl.comp f) ∘ a) m.roots).det=0) :
    let x := fun j => pos 0 (r j)
    let y := fun j => pos 1 (s j)
    let F := fallback (cof x y) D
    F≠0 ∧ F.totalDegree ≤ 12 ∧
      ∀ (T : Type*) [Field T] (g : PlanePoly k →+* T) (u : Fin 4 → T) (H₁ H₂ A : T),
        (∀ i,u i^2=g (D i)) →
        (∀ i,g (x i)*H₁+g (y i)*H₂-u i*A=g (b i)-u i*g (a i)) →
        A≠g (a 3) → g F=0 := by
  dsimp only
  exact ⟨fallback_ne_zero f hf D m hind _ ⟨2,position_cofactor_nonzero r s distinct⟩,
    fallback_degree _ _ (position_cofactor_degrees r s) hD,
    fun _ _ g u h k A => specialized_fallback f hf D m hind _ _ b a gen g u h k A⟩
end Position
end
end PlanarUnitDistances.AnchorFallback