import PlanarUnitDistances.HomogeneousMacaulay

namespace PlanarUnitDistances.BlockMacaulay
open HomogeneousMacaulay Finset MvPolynomial
open scoped Classical Matrix
noncomputable section
variable {q : ℕ} (ℓ : Coord q)

/-- All other admissible input blocks precede the distinguished block. -/
def late (a : Row q) : Coord q :=
  if h : ∃i, i≠ℓ ∧ formDegree i ≤ a.val i then h.choose else ℓ

theorem late_divides (a : Row q) : formDegree (late ℓ a) ≤ a.val (late ℓ a) := by
  unfold late
  split
  next h => exact h.choose_spec.2
  next h =>
    have hc : chosen a=ℓ := by
      by_contra hn
      exact h ⟨chosen a,hn,chosen_divides a⟩
    simpa only [←hc] using chosen_divides a

theorem off_small (a : Row q) (ha : late ℓ a=ℓ) (j : Coord q) (hj : j≠ℓ) : a.val j < formDegree j := by
  by_contra! hn
  have e : ∃i, i≠ℓ ∧ formDegree i ≤ a.val i := ⟨j,hj,hn⟩
  rw [late,dite_eq_left e] at ha
  exact e.choose_spec.1 ha

def rest (a : Row q) : Coord q →₀ ℕ :=
  a.val-(pureMon (late ℓ a) (formDegree (late ℓ a))).val

theorem rest_add (a : Row q) :
    rest ℓ a+(pureMon (late ℓ a) (formDegree (late ℓ a))).val=a.val :=
  tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (late_divides ℓ a))

def index (a : Row q) (m : Mon q (formDegree (late ℓ a))) : Row q := by
  refine ⟨rest ℓ a+m.val,mem_finsuppAntidiag.mpr ⟨?_,subset_univ _⟩⟩
  calc
    (∑i, (rest ℓ a+m.val) i) = (∑i,rest ℓ a i)+formDegree (late ℓ a) := by
      simp only [Finsupp.add_apply,sum_add_distrib,sum_exponents]
    _ = ∑i, (rest ℓ a+(pureMon (late ℓ a) (formDegree (late ℓ a))).val) i := by
      simp only [Finsupp.add_apply,sum_add_distrib,sum_exponents]
    _ = q+1 := by rw [rest_add,sum_exponents]

@[simp] theorem index_pure (a : Row q) :
    index ℓ a (pureMon (late ℓ a) (formDegree (late ℓ a)))=a := Subtype.ext (rest_add ℓ a)

def blockMatrix {R : Type*} [CommRing R] (A : Coefficients q R) : Matrix (Row q) (Row q) R :=
  fun a b => ∑m, if index ℓ a m=b then A (late ℓ a) m else 0

private def monomialValue {R : Type*} [CommRing R] (x : Coord q → R) (m : Coord q →₀ ℕ) : R :=
  eval x (monomial m 1)

private theorem value_add {R : Type*} [CommRing R] (x : Coord q → R) (a b : Coord q →₀ ℕ) :
    monomialValue x (a+b)=monomialValue x a*monomialValue x b := by
  unfold monomialValue
  rw [←map_mul,monomial_mul_monomial,mul_one]

theorem block_evaluation {R : Type*} [CommRing R] (A : Coefficients q R)
    (x : Coord q → R) (a : Row q) :
    (blockMatrix ℓ A *ᵥ (fun b => monomialValue x b.val)) a =
      monomialValue x (rest ℓ a)*eval x (form A (late ℓ a)) := by
  change (∑b, (∑m, if index ℓ a m=b then A (late ℓ a) m else 0)*monomialValue x b.val)=_
  simp_rw [sum_mul]
  rw [sum_comm]
  simp only [ite_mul,zero_mul,sum_ite_eq,mem_univ,ite_true,form,map_sum,map_mul,eval_C,mul_sum]
  apply sum_congr rfl
  intro m _
  change A (late ℓ a) m * monomialValue x (rest ℓ a+m.val)=_
  rw [value_add]
  unfold monomialValue
  ring

/-- A common projective point kills this determinant, including at infinity. -/
theorem common_zero {K : Type*} [CommRing K] [IsDomain K] (A : Coefficients q K)
    (x : Coord q → K) (nonzero : ∃i,x i≠0) (root : ∀i,eval x (form A i)=0) : (blockMatrix ℓ A).det=0 := by
  obtain ⟨i,hi⟩ := nonzero
  have annihilates : (blockMatrix ℓ A *ᵥ fun b => monomialValue x b.val)=0 := by
    ext a
    rw [block_evaluation,root,mul_zero]
    rfl
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors annihilates (i:=pureMon i (q+1))
  apply mem_nonZeroDivisors_of_ne_zero
  change eval x (monomial (Finsupp.single i (q+1)) (1:K))≠0
  rw [←X_pow_eq_monomial,map_pow,eval_X]
  exact pow_ne_zero _ hi

/-- At X₀ and X₁²,…,X_q² this minor is exactly the identity matrix. -/
theorem diagonal_system (R : Type*) [CommRing R] : blockMatrix ℓ (monomialSystem q R)=1 := by
  ext a b
  change (∑m, if index ℓ a m=b then (if m=pureMon (late ℓ a) (formDegree (late ℓ a)) then (1:R) else 0) else 0)=_
  rw [Finset.sum_eq_single (pureMon (late ℓ a) (formDegree (late ℓ a)))]
  · simp [Matrix.one_apply]
  · intro m _ hm
    simp [hm]
  · simp

theorem map_blockMatrix {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (A : Coefficients q R) :
    (blockMatrix ℓ A).map f = blockMatrix ℓ (fun i m => f (A i m)) := by
  ext a b
  simp [blockMatrix,apply_ite f]

def minor : MvPolynomial (Parameter q) ℤ :=
  (blockMatrix ℓ (fun i m => (X ⟨i,m⟩ : MvPolynomial (Parameter q) ℤ))).det

theorem eval_minor {R : Type*} [CommRing R] (A : Coefficients q R) :
    eval₂Hom (Int.castRingHom R) (fun e : Parameter q => A e.1 e.2) (minor ℓ)=(blockMatrix ℓ A).det := by
  let f := eval₂Hom (Int.castRingHom R) (fun e : Parameter q => A e.1 e.2)
  change f (blockMatrix ℓ (fun i m => (X ⟨i,m⟩ : MvPolynomial (Parameter q) ℤ))).det=_
  rw [RingHom.map_det]
  change ((blockMatrix ℓ (fun i m => (X ⟨i,m⟩ : MvPolynomial (Parameter q) ℤ))).map f).det=_
  rw [map_blockMatrix]
  simp [f]

theorem minor_ne_zero : minor ℓ≠0 := by
  intro zero
  have test := eval_minor ℓ (monomialSystem q ℤ)
  rw [zero,map_zero,diagonal_system,Matrix.det_one] at test
  exact zero_ne_one test

def assigned : Finset (Row q) := univ.filter fun a => late ℓ a=ℓ

private def encode (a : ↥(assigned ℓ)) (j : Coord q) : Fin (if j=ℓ then 1 else formDegree j) := by
  by_cases h : j=ℓ
  · exact ⟨0,by simp [h]⟩
  · exact ⟨a.val.val j,by simpa [h] using off_small ℓ a.val (mem_filter.mp a.property).2 j h⟩

/-- The deleted coordinate is determined by the known sum of all exponents.
Every other exponent is strictly smaller than its form degree. -/
private theorem encode_injective : Function.Injective (encode ℓ) := by
  intro a b h
  have off (j : Coord q) (hj : j≠ℓ) : a.val.val j=b.val.val j := by
    have e := congrArg Fin.val (congrFun h j)
    simpa [encode,hj] using e
  have other : ∑ j ∈ univ.erase ℓ, a.val.val j = ∑ j ∈ univ.erase ℓ, b.val.val j :=
    sum_congr rfl (fun j hj => off j (mem_erase.mp hj).1)
  have eq := (sum_exponents a.val).trans (sum_exponents b.val).symm
  rw [←sum_erase_add univ _ (mem_univ ℓ),←sum_erase_add univ _ (mem_univ ℓ),other] at eq
  apply Subtype.ext
  apply Subtype.ext
  ext j
  by_cases hj : j=ℓ
  · subst j
    exact Nat.add_left_cancel eq
  · exact off j hj

theorem assigned_bound : (assigned ℓ).card ≤ ∏ j : Coord q, (if j=ℓ then 1 else formDegree j) := by
  have comparison := Fintype.card_le_of_injective _ (encode_injective ℓ)
  simpa only [Fintype.card_coe,Fintype.card_pi,Fintype.card_fin] using comparison

theorem off_product : (∏ j : Coord q, if j=ℓ then 1 else formDegree j) =
    ℓ.elim (2^q) (fun _ => 2^(q-1)) := by
  cases ℓ with
  | none => simp [Fintype.prod_option,formDegree]
  | some b =>
    rw [Fintype.prod_option]
    simp [formDegree,Finset.prod_ite,Finset.filter_ne']

abbrev Universal (q : ℕ) := MvPolynomial (Parameter q) ℤ

/-- Scale exactly one block by a fresh parameter. Its univariate degree
measures the total degree in that block, retaining every other coefficient. -/
def blockScale : Universal q →+* Polynomial (Universal q) :=
  eval₂Hom (Polynomial.C.comp C) (fun e => Polynomial.X^(if e.1=ℓ then 1 else 0)*Polynomial.C (X e))

private def variableTable : Coefficients q (Universal q) := fun i m => X ⟨i,m⟩

private def blockPower (a : Row q) : ℕ := if late ℓ a=ℓ then 1 else 0

private theorem entry_scaled (a b : Row q) :
    blockScale ℓ (blockMatrix ℓ variableTable a b) =
      (Polynomial.X : Polynomial (Universal q))^(blockPower ℓ a) * Polynomial.C (blockMatrix ℓ variableTable a b) := by
  unfold blockMatrix
  rw [map_sum,map_sum,mul_sum]
  apply sum_congr rfl
  intro m _
  by_cases h : index ℓ a m=b
  · simp only [h,ite_true,variableTable,blockScale,MvPolynomial.eval₂Hom_X',blockPower]
  · simp only [h,ite_false,map_zero,mul_zero]

private theorem det_scale_rows {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A B : Matrix ι ι R) (v : ι → R) (h : ∀a b,A a b=v a*B a b) : A.det=(∏a,v a)*B.det := by
  have heq : A=Matrix.of (fun a b => v a*B a b) := Matrix.ext h
  rw [heq,Matrix.det_mul_column]

theorem blockScale_minor : blockScale ℓ (minor ℓ) =
    Polynomial.X^(assigned ℓ).card * Polynomial.C (minor ℓ) := by
  have sum : (∑ a, blockPower ℓ a)=(assigned ℓ).card := (Finset.card_filter _ _).symm
  change blockScale ℓ (blockMatrix ℓ variableTable).det = _ * Polynomial.C (blockMatrix ℓ variableTable).det
  rw [RingHom.map_det, RingHom.map_det]
  change ((blockMatrix ℓ variableTable).map (blockScale ℓ)).det = _ * ((blockMatrix ℓ variableTable).map Polynomial.C).det
  rw [←sum,←prod_pow_eq_pow_sum]
  apply det_scale_rows
  intro a b
  simp only [Matrix.map_apply]
  exact entry_scaled ℓ a b

theorem blockScale_minor_ne_zero : blockScale ℓ (minor ℓ)≠0 := by
  rw [blockScale_minor]
  exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Polynomial.C_ne_zero.mpr (minor_ne_zero ℓ))

/-- Every common divisor inherits the saving in the same distinguished
block, even though a different minor is used for every block. -/
theorem block_degree_of_dvd {F : Universal q} (h : F ∣ minor ℓ) :
    (blockScale ℓ F).natDegree ≤ ℓ.elim (2^q) (fun _ => 2^(q-1)) := by
  have le := Polynomial.natDegree_le_of_dvd (map_dvd (blockScale ℓ) h) (blockScale_minor_ne_zero ℓ)
  rw [blockScale_minor,Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero)
    (Polynomial.C_ne_zero.mpr (minor_ne_zero ℓ))] at le
  simp only [Polynomial.natDegree_X_pow,Polynomial.natDegree_C,add_zero] at le
  exact le.trans ((assigned_bound ℓ).trans_eq (off_product ℓ))

def blockExponent (d : Parameter q →₀ ℕ) : ℕ :=
  ∑ e ∈ d.support, (if e.1=ℓ then 1 else 0)*d e

theorem blockScale_monomial (d : Parameter q →₀ ℕ) (a : ℤ) :
    blockScale ℓ (monomial d a) = Polynomial.X^(blockExponent ℓ d)*Polynomial.C (monomial d a) := by
  rw [blockScale,eval₂Hom_monomial]
  simp only [RingHom.comp_apply,Finsupp.prod,mul_pow,←pow_mul,←map_pow,prod_mul_distrib,
    prod_pow_eq_pow_sum,←map_prod,prod_X_pow_eq_monomial]
  rw [mul_left_comm,←map_mul,C_mul_monomial,mul_one]
  rfl

theorem scaled_coefficient (F : Universal q) (d : Parameter q →₀ ℕ) (k : ℕ) :
    ((blockScale ℓ F).coeff k).coeff d = if blockExponent ℓ d=k then F.coeff d else 0 := by
  induction F using MvPolynomial.induction_on' with
  | monomial e a =>
    rw [blockScale_monomial,mul_comm,Polynomial.coeff_C_mul_X_pow]
    by_cases he : e=d
    · subst e
      by_cases hk : k=blockExponent ℓ d
      · simp [hk]
      · simp [hk,Ne.symm hk]
    · by_cases hk : k=blockExponent ℓ e <;> by_cases hd : blockExponent ℓ d=k <;> simp [hk,hd,he]
  | add F G hF hG =>
    simp only [map_add,Polynomial.coeff_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hF,hG]
    split <;> simp

theorem support_exponent_le (F : Universal q) {d : Parameter q →₀ ℕ} (hd : d ∈ F.support) :
    blockExponent ℓ d ≤ (blockScale ℓ F).natDegree := by
  by_contra! small
  have eq := scaled_coefficient ℓ F d (blockExponent ℓ d)
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt small,AddMonoidAlgebra.coeff_zero,ite_eq_left rfl] at eq
  exact (mem_support_iff.mp hd) eq.symm

/-- A common divisor is bounded in total coefficient degree, although
the original determinants have much larger total degree individually. -/
theorem totalDegree_of_common_divisor {F : Universal q} (dvd : ∀ℓ, F ∣ minor ℓ) :
    F.totalDegree ≤ 2^q+q*2^(q-1) := by
  apply Finset.sup_le
  intro d hd
  have eq : (∑ b : Coord q, blockExponent b d) = d.sum (fun _ k => k) := by
    unfold blockExponent Finsupp.sum
    rw [sum_comm]
    apply sum_congr rfl
    intro e _
    simp [ite_mul]
  rw [←eq]
  calc
    _ ≤ ∑ b : Coord q, b.elim (2^q) (fun _ => 2^(q-1)) :=
      sum_le_sum fun b _ => (support_exponent_le b F hd).trans (block_degree_of_dvd b (dvd b))
    _ = _ := by simp [Fintype.sum_option]

theorem degree_budget {F : Universal q} (dvd : ∀ℓ, F ∣ minor ℓ) (hq : q≤98) : F.totalDegree < 2^104 := by
  apply (totalDegree_of_common_divisor dvd).trans_lt
  have h₂ : 2^q ≤ 2^98 := Nat.pow_le_pow_right (by decide) hq
  have h₃ : 2^(q-1) ≤ 2^97 := Nat.pow_le_pow_right (by decide) (by omega)
  exact (Nat.add_le_add h₂ (Nat.mul_le_mul hq h₃)).trans_lt (by decide)


end
end PlanarUnitDistances.BlockMacaulay
