import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Data.Finsupp.Order
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-! A square Macaulay minor for one linear form and q quadrics in q+1
projective coordinates. Each row is a monomial multiple of an actual input
form. The determinant is an integral universal polynomial in the coefficients. -/
namespace PlanarUnitDistances.HomogeneousMacaulay
open Finset MvPolynomial
open scoped Classical Matrix
noncomputable section

abbrev Coord (q : ℕ) := Option (Fin q)
abbrev Mon (q n : ℕ) := ↥(finsuppAntidiag (univ : Finset (Coord q)) n)
abbrev Row (q : ℕ) := Mon q (q+1)

def formDegree {q : ℕ} : Coord q → ℕ
  | none => 1
  | some _ => 2

abbrev Coefficients (q : ℕ) (R : Type*) := ∀ i : Coord q, Mon q (formDegree i) → R

theorem sum_exponents {q n : ℕ} (a : Mon q n) : ∑i, a.val i = n :=
  (mem_finsuppAntidiag.mp a.property).1

def pureMon {q : ℕ} (i : Coord q) (d : ℕ) : Mon q d :=
  ⟨Finsupp.single i d, mem_finsuppAntidiag.mpr ⟨by simp [Finsupp.single_apply],subset_univ _⟩⟩

private theorem has_divisor {q : ℕ} (a : Row q) : ∃i, formDegree i ≤ a.val i := by
  by_contra! h
  have z : a.val none=0 := by have ht := h none; change _ < 1 at ht; omega
  have bound (i : Fin q) : a.val (some i) ≤ 1 := by
    have ht := h (some i)
    change _ < 2 at ht
    omega
  have sum := sum_exponents a
  rw [Fintype.sum_option,z,zero_add] at sum
  apply Nat.not_succ_le_self q
  calc q+1 = ∑ i : Fin q, a.val (some i) := sum.symm
       _ ≤ ∑ _ : Fin q, (1 : ℕ) := Finset.sum_le_sum (fun i _ => bound i)
       _ = q := by simp

private def quadraticDivisors {q : ℕ} (a : Row q) : Finset (Fin q) :=
  univ.filter (fun i => 2 ≤ a.val (some i))

private theorem quadraticDivisors_nonempty {q : ℕ} (a : Row q) (h : ¬1 ≤ a.val none) :
    (quadraticDivisors a).Nonempty := by
  obtain ⟨i,hi⟩ := has_divisor a
  cases i with
  | none => exact False.elim (h hi)
  | some j => exact ⟨j,mem_filter.mpr ⟨mem_univ _,hi⟩⟩

/-- Prefer the linear monomial; otherwise take the square with least index. -/
def chosen {q : ℕ} (a : Row q) : Coord q :=
  if h : 1 ≤ a.val none then none
  else some ((quadraticDivisors a).min' (quadraticDivisors_nonempty a h))

theorem chosen_divides {q : ℕ} (a : Row q) : formDegree (chosen a) ≤ a.val (chosen a) := by
  unfold chosen
  split
  next h => exact h
  next h => exact (mem_filter.mp (min'_mem _ (quadraticDivisors_nonempty a h))).2

def rowMultiplier {q : ℕ} (a : Row q) : Coord q →₀ ℕ :=
  a.val-(pureMon (chosen a) (formDegree (chosen a))).val

theorem multiplier_add {q : ℕ} (a : Row q) :
    rowMultiplier a+(pureMon (chosen a) (formDegree (chosen a))).val=a.val :=
  tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (chosen_divides a))

def column {q : ℕ} (a : Row q) (m : Mon q (formDegree (chosen a))) : Row q := by
  refine ⟨rowMultiplier a+m.val,mem_finsuppAntidiag.mpr ⟨?_,subset_univ _⟩⟩
  calc
    (∑i, (rowMultiplier a+m.val) i) = (∑i,rowMultiplier a i)+formDegree (chosen a) := by
      simp only [Finsupp.add_apply,sum_add_distrib,sum_exponents]
    _ = ∑i, (rowMultiplier a+(pureMon (chosen a) (formDegree (chosen a))).val) i := by
      simp only [Finsupp.add_apply,sum_add_distrib,sum_exponents]
    _ = q+1 := by rw [multiplier_add,sum_exponents]

@[simp] theorem column_pure {q : ℕ} (a : Row q) :
    column a (pureMon (chosen a) (formDegree (chosen a)))=a := Subtype.ext (multiplier_add a)

def matrix {q : ℕ} {R : Type*} [CommRing R] (A : Coefficients q R) : Matrix (Row q) (Row q) R :=
  fun a b => ∑m, if column a m=b then A (chosen a) m else 0

def form {q : ℕ} {R : Type*} [CommRing R] (A : Coefficients q R) (i : Coord q) : MvPolynomial (Coord q) R :=
  ∑m, C (A i m)*monomial m.val 1

private def monomialValue {q : ℕ} {R : Type*} [CommRing R] (x : Coord q → R) (m : Coord q →₀ ℕ) : R :=
  eval x (monomial m 1)

private theorem value_add {q : ℕ} {R : Type*} [CommRing R] (x : Coord q → R) (a b : Coord q →₀ ℕ) :
    monomialValue x (a+b)=monomialValue x a*monomialValue x b := by
  unfold monomialValue
  rw [←map_mul,monomial_mul_monomial,mul_one]

theorem matrix_evaluation {q : ℕ} {R : Type*} [CommRing R] (A : Coefficients q R)
    (x : Coord q → R) (a : Row q) :
    (matrix A *ᵥ (fun b => monomialValue x b.val)) a =
      monomialValue x (rowMultiplier a)*eval x (form A (chosen a)) := by
  change (∑b, (∑m, if column a m=b then A (chosen a) m else 0)*monomialValue x b.val)=_
  simp_rw [sum_mul]
  rw [sum_comm]
  simp only [ite_mul,zero_mul,sum_ite_eq,mem_univ,ite_true,form,map_sum,map_mul,eval_C,mul_sum]
  apply sum_congr rfl
  intro m _
  change A (chosen a) m * monomialValue x (rowMultiplier a+m.val)=_
  rw [value_add]
  unfold monomialValue
  ring


def monomialSystem (q : ℕ) (R : Type*) [CommRing R] : Coefficients q R :=
  fun i m => if m=pureMon i (formDegree i) then 1 else 0

/-- At X₀ and X₁²,…,X_q² the chosen minor is exactly the identity matrix. -/
theorem monomial_matrix (q : ℕ) (R : Type*) [CommRing R] : matrix (monomialSystem q R)=1 := by
  ext a b
  change (∑m, if column a m=b then (if m=pureMon (chosen a) (formDegree (chosen a)) then (1:R) else 0) else 0)=_
  rw [Finset.sum_eq_single (pureMon (chosen a) (formDegree (chosen a)))]
  · simp [Matrix.one_apply]
  · intro m _ hm
    simp [hm]
  · simp

theorem map_matrix {q : ℕ} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (A : Coefficients q R) :
    (matrix A).map f = matrix (fun i m => f (A i m)) := by
  ext a b
  simp [matrix,apply_ite f]

abbrev Parameter (q : ℕ) := Sigma (fun i : Coord q => Mon q (formDegree i))

def universalDeterminant (q : ℕ) : MvPolynomial (Parameter q) ℤ :=
  (matrix (q:=q) (fun i m => (X ⟨i,m⟩ : MvPolynomial (Parameter q) ℤ))).det

theorem specialize {q : ℕ} {R : Type*} [CommRing R] (A : Coefficients q R) :
    eval₂Hom (Int.castRingHom R) (fun e : Parameter q => A e.1 e.2) (universalDeterminant q)=(matrix A).det := by
  let f := eval₂Hom (Int.castRingHom R) (fun e : Parameter q => A e.1 e.2)
  change f (matrix (q:=q) (fun i m => (X ⟨i,m⟩ : MvPolynomial (Parameter q) ℤ))).det=_
  rw [RingHom.map_det]
  change ((matrix (q:=q) (fun i m => (X ⟨i,m⟩ : MvPolynomial (Parameter q) ℤ))).map f).det=_
  rw [map_matrix]
  simp [f]


theorem matrix_size (q : ℕ) : Fintype.card (Row q)=(2*q+1).choose (q+1) := by
  rw [Fintype.card_coe,Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [card_univ,Fintype.card_option,Fintype.card_fin]
  congr 1
  omega

/-- The coefficient table of homogeneous input polynomials recovers the original forms. -/
theorem form_of_coeff {q : ℕ} {R : Type*} [CommRing R] (F : Coord q → MvPolynomial (Coord q) R)
    (i : Coord q) (hF : (F i).IsHomogeneous (formDegree i)) :
    form (fun j m => (F j).coeff m.val) i=F i := by
  ext e
  simp only [form,coeff_sum,coeff_C_mul,coeff_monomial]
  by_cases h : e ∈ finsuppAntidiag (univ : Finset (Coord q)) (formDegree i)
  · let m : Mon q (formDegree i) := ⟨e,h⟩
    rw [sum_eq_single m]
    · simp [m]
    · intro n _ hn
      have hn' : n.val ≠ e := fun he => hn (Subtype.ext he)
      simp [hn']
    · simp
  · have he : e.degree ≠ formDegree i := by
      intro he
      exact h (mem_finsuppAntidiag.mpr ⟨(Finsupp.degree_eq_sum e).symm.trans he,subset_univ _⟩)
    rw [hF.coeff_eq_zero he]
    apply sum_eq_zero
    intro m _
    have hm : m.val ≠ e := fun he => h (he ▸ m.property)
    simp [hm]

private theorem matrix_add_scaled {q : ℕ} {R : Type*} [CommRing R]
    (A B : Coefficients q R) (t : R) (a b : Row q) :
    matrix (fun i m => A i m + t * B i m) a b = matrix A a b + t * matrix B a b := by
  simp only [matrix,mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro m _
  split <;> simp_all

/-- For a linear test and q homogeneous quadrics, adding U times their respective
pure monomials gives a monic determinant in U, over any nontrivial coefficient ring. -/
theorem diagonal_deformation {q : ℕ} {R : Type*} [CommRing R] (A : Coefficients q R) :
    (matrix (fun i m => Polynomial.C (A i m) +
      Polynomial.X * monomialSystem q (Polynomial R) i m)).det = (-matrix A).charpoly := by
  apply congrArg Matrix.det
  ext a b
  rw [matrix_add_scaled,←map_matrix,monomial_matrix,Matrix.charmatrix_apply]
  by_cases h : a=b <;> simp [Matrix.one_apply,h,add_comm]

/-- Deform the quadrics by εXᵢ², and the additional linear form by −TX₀. -/
def deformed {q : ℕ} {R : Type*} [CommRing R] (A : Coefficients q R)
    (ε T : R) : Coefficients q R := fun i m =>
  A i m + (i.elim (-T) (fun _ => ε)) * monomialSystem q R i m

theorem map_deformed {q : ℕ} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Coefficients q R) (ε T : R) (i : Coord q) (m : Mon q (formDegree i)) :
    f (deformed A ε T i m)=deformed (fun j n => f (A j n)) (f ε) (f T) i m := by
  cases i <;> simp [deformed,monomialSystem,apply_ite f]

theorem form_deformed {q : ℕ} {R : Type*} [CommRing R] (A : Coefficients q R)
    (ε T : R) (i : Coord q) :
    form (deformed A ε T) i = form A i +
      C (i.elim (-T) (fun _ => ε)) * X i ^ formDegree i := by
  simp only [form,deformed,map_add,map_mul,add_mul,sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single (pureMon i (formDegree i))]
  · simp [monomialSystem,pureMon,X_pow_eq_monomial]
  · intro m _ hm
    simp [monomialSystem,hm]
  · simp

/-- R[ε][T] has independent deformation and coordinate parameters. -/
def eliminationPolynomial {q : ℕ} {R : Type*} [CommRing R] (A : Coefficients q R) :
    Polynomial (Polynomial R) :=
  (matrix (deformed (fun i m => Polynomial.C (Polynomial.C (A i m)))
    (Polynomial.C Polynomial.X) Polynomial.X)).det


/-- On the diagonal T=−ε, the two-parameter determinant specializes to a monic
polynomial of degree exactly the number of Macaulay monomials. -/
theorem elimination_diagonal {q : ℕ} {R : Type*} [CommRing R] (A : Coefficients q R) :
    Polynomial.evalRingHom (-Polynomial.X) (eliminationPolynomial A) = (-matrix A).charpoly := by
  unfold eliminationPolynomial
  rw [RingHom.map_det]
  change ((matrix _).map _).det = _
  rw [map_matrix,←diagonal_deformation]
  congr 2
  funext i m
  rw [map_deformed]
  cases i <;> simp [deformed]

theorem elimination_nonzero {q : ℕ} {R : Type*} [CommRing R] [Nontrivial R] (A : Coefficients q R) :
    eliminationPolynomial A≠0 := by
  intro h
  have hz := elimination_diagonal A
  rw [h,map_zero] at hz
  exact (-matrix A).charpoly_monic.ne_zero hz.symm


end
end PlanarUnitDistances.HomogeneousMacaulay
