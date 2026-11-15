import PlanarUnitDistances.QuadraticKummerInput
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-! Orders at finite points of a rationally parametrized curve. -/
namespace PlanarUnitDistances.RationalPrivateZeros
open Polynomial IsDedekindDomain.HeightOneSpectrum
open scoped Polynomial
noncomputable section
variable {K : Type*} [Field K]

def linearPrime (s : K) : IsDedekindDomain.HeightOneSpectrum K[X] where
  asIdeal := Ideal.span {X-C s}
  isPrime := Ideal.span_singleton_prime (X_sub_C_ne_zero s) |>.mpr (prime_X_sub_C s)
  ne_bot := Ideal.span_singleton_eq_bot.not.mpr (X_sub_C_ne_zero s)

/-- The additive order is the negative log of Mathlib's multiplicative
valuation. The restriction to nonzero functions is a group homomorphism. -/
def order (s : K) : (RatFunc K)ˣ →* Multiplicative ℤ where
  toFun f := Multiplicative.ofAdd (-WithZero.log ((linearPrime s).valuation (RatFunc K) (f:RatFunc K)))
  map_one' := by simp
  map_mul' f g := by
    simp only [Units.val_mul,map_mul]
    rw [WithZero.log_mul (by simp [f.ne_zero]) (by simp [g.ne_zero]),neg_add]
    rfl

private theorem away (s : K) (p : K[X]) (h : p.eval s≠0) :
    (linearPrime s).intValuation p=1 := by
  rw [intValuation_eq_one_iff_mem_primeCompl]
  change p ∉ Ideal.span {X-C s}
  rwa [Ideal.mem_span_singleton,dvd_iff_isRoot]

private theorem simple (s : K) (p : K[X]) (h : p.eval s=0)
    (dh : p.derivative.eval s≠0) :
    (linearPrime s).intValuation p=WithZero.exp (-1:ℤ) := by
  obtain ⟨q,rfl⟩ := dvd_iff_isRoot.mpr h
  have hq : q.eval s≠0 := by simpa using dh
  rw [map_mul,intValuation_singleton _ (X_sub_C_ne_zero s) rfl,away _ _ hq,mul_one]

/-- Actual arithmetic of private points on a rational parameter line.
All numerator and denominator evaluations occur over the final constant
field, including when it has already been enlarged by anchor parameters. -/
theorem private_orders_of_simple_zeros (P Q : Fin 4 → K[X])
    (D : Fin 4 → (RatFunc K)ˣ)
    (formula : ∀ i,(D i:RatFunc K)=algebraMap K[X] (RatFunc K) (P i) /
      algebraMap K[X] (RatFunc K) (Q i))
    (s : Fin 4 → K) (hroot : ∀ i,(P i).eval (s i)=0)
    (hsimple : ∀ i,(P i).derivative.eval (s i)≠0)
    (hother : ∀ i j,j≠i → (P j).eval (s i)≠0)
    (hden : ∀ i j,(Q j).eval (s i)≠0) : FourRowObstruction.PrivateOrders D := by
  intro i
  refine ⟨order (s i),?_,?_⟩
  · change -WithZero.log ((linearPrime _).valuation (RatFunc K) (D i:RatFunc K))=1
    rw [formula,map_div₀,valuation_of_algebraMap,valuation_of_algebraMap,
      simple _ _ (hroot i) (hsimple i),away _ _ (hden i i),div_one]
    simp
  · intro j hj
    change -WithZero.log ((linearPrime _).valuation (RatFunc K) (D j:RatFunc K))=0
    rw [formula,map_div₀,valuation_of_algebraMap,valuation_of_algebraMap,
      away _ _ (hother i j hj),away _ _ (hden i j)]
    simp

private theorem difference_not_constant {k : Type*} [Field k] [Algebra k K]
    (a : Fin 4 → K) (ind : AlgebraicIndependent k a) {i j : Fin 4} (hne : i≠j) (d : k) :
    a i-a j≠algebraMap k K d := by
  intro h
  let p : MvPolynomial (Fin 4) k := MvPolynomial.X i-MvPolynomial.X j-MvPolynomial.C d
  have zero : p=0 := ind.eq_zero_of_aeval_eq_zero _ (by simp [p,h])
  have e := congrArg (MvPolynomial.pderiv i) zero
  simp [p,MvPolynomial.pderiv_X_of_ne hne.symm] at e

def lineChord (e a : K) : K[X] := C e*(X-C a)^2

/-- The same-line case of the private-valuation lemma, with the actual four
generic anchor abscissas. The intercept cancels from the squared distance.
The final constant field K may contain arbitrarily many other elements. -/
theorem line_private_orders {k : Type*} [Field k] [CharZero k] [CharZero K] [Algebra k K]
    (e c : k) (ec : e*c^2=4) (a : Fin 4 → K) (ind : AlgebraicIndependent k a) :
    ∃ D : Fin 4 → (RatFunc K)ˣ, FourRowObstruction.PrivateOrders D ∧ ∀ i,
      let l := lineChord (algebraMap k K e) (a i)
      (D i:RatFunc K)=algebraMap K[X] (RatFunc K) (l*(l-4)) := by
  let E := algebraMap k K e
  let C₀ := algebraMap k K c
  have hc : E*C₀^2=4 := by simpa only [E,C₀,map_mul,map_pow,map_ofNat] using congrArg (algebraMap k K) ec
  have e0 : E≠0 := by intro h; rw [h] at hc; norm_num at hc
  have c0 : C₀≠0 := by intro h; rw [h] at hc; norm_num at hc
  let l i := lineChord E (a i)
  let P i := l i*(l i-4)
  let s i := a i+C₀
  have val (i j) : (l j).eval (s i)=E*(a i+C₀-a j)^2 := by simp [l,s,lineChord]
  have here (i) : (l i).eval (s i)=4 := by simpa [val] using hc
  have root (i) : (P i).eval (s i)=0 := by simp [P,here]
  have deriv (i) : (l i).derivative.eval (s i)=2*E*C₀ := by
    simp [l,lineChord,s,derivative_pow]; ring
  have simple_root (i) : (P i).derivative.eval (s i)≠0 := by
    simp [P,derivative_mul,here,deriv,e0,c0]
  have other (i j) (ne : j≠i) : (P j).eval (s i)≠0 := by
    let z := a i+C₀-a j
    have avoid (d : k) : a i-a j≠algebraMap k K d := difference_not_constant a ind ne.symm d
    have z0 : z≠0 := by
      intro h
      apply avoid (-c)
      rw [map_neg]; change a i-a j= -C₀
      dsimp [z] at h; linear_combination h
    have nz : E*z^2≠4 := by
      intro h
      have f : (z-C₀)*(z+C₀)=0 := by
        apply mul_left_cancel₀ e0
        linear_combination h-hc
      rcases mul_eq_zero.mp f with p|p
      · apply avoid 0
        rw [map_zero]
        dsimp [z] at p; linear_combination p
      · apply avoid (-(c+c))
        rw [map_neg,map_add]
        change a i-a j= -(C₀+C₀)
        dsimp [z] at p; linear_combination p
    change (l j*(l j-4)).eval (s i)≠0
    simpa [val, ← show a i+C₀-a j=z from rfl] using
      mul_ne_zero (mul_ne_zero e0 (pow_ne_zero 2 z0)) (sub_ne_zero.mpr nz)
  have pne i : P i≠0 := by
    intro h
    have := simple_root i
    simp [h] at this
  let D i := Units.mk0 (algebraMap K[X] (RatFunc K) (P i))
    (by simpa only [map_zero] using (RatFunc.algebraMap_injective K).ne (pne i))
  refine ⟨D,private_orders_of_simple_zeros P (fun _ => 1) D (by simp [D]) s
    root simple_root other (by simp),fun i => rfl⟩
end
end PlanarUnitDistances.RationalPrivateZeros
