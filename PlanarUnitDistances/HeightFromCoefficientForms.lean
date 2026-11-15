import PlanarUnitDistances.StationaryUniformHeight

namespace PlanarUnitDistances.TorusCritical
open Finset MvPolynomial Real Height NumberField ArithmeticIntersection EliminantHeight
open scoped Classical
noncomputable section

private def assemble {R : Type*} [Semiring R] {n : ℕ} (g : Fin n → R) : Polynomial R :=
  ∑ j, Polynomial.monomial j.val (g j)

private theorem assemble_coeff {R : Type*} [Semiring R] {n : ℕ} (g : Fin n → R) (j : ℕ) :
    (assemble g).coeff j = if h : j < n then g ⟨j,h⟩ else 0 := by
  classical
  simp only [assemble, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  split
  next h =>
    rw [sum_eq_single (⟨j,h⟩ : Fin n)]
    · simp
    · intro i _ hi
      have ne : i.val ≠ j := fun e => hi (Fin.ext e)
      simp [ne]
    · simp
  next h =>
    apply sum_eq_zero
    intro i _
    have ne : i.val ≠ j := by intro eq; exact h (eq ▸ i.isLt)
    simp [ne]

private theorem relation_evaluation {K A : Type*} [Field K] (a : A → K)
    (F : MvPolynomial (Option A) ℤ) :
    outputPolynomial a (MvPolynomial.map (Int.castRingHom K) F) =
      Polynomial.map (aeval (R:=ℤ) a).toRingHom (optionEquivLeft ℤ A F) := by
  induction F using MvPolynomial.induction_on with
  | C r => simp [outputPolynomial]
  | add p q hp hq => simp only [map_add,Polynomial.map_add,hp,hq]
  | mul_X p j hp =>
    simp only [map_mul,MvPolynomial.map_X,Polynomial.map_mul,hp]
    cases j <;> simp [outputPolynomial]

private theorem log_nat_cap (L m : ℕ) (pos : 0 < L) (size : L ≤ 2^m) : log (L:ℝ) ≤ m := by
  have hr : (L:ℝ) ≤ (2:ℝ)^m := by exact_mod_cast size
  apply (Real.log_le_log (by exact_mod_cast pos) hr).trans
  rw [Real.log_pow]
  have htwo : log 2 ≤ 1 := (Real.log_le_sub_one_of_pos (x:=(2:ℝ)) (by norm_num)).trans_eq (by norm_num)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (α:=ℝ) m)

/-- Coefficient representations may depend on the particular root and specialization.
    The bound needs only their uniform degree and coefficient sizes. -/
theorem ratio_height_from_coefficient_forms {I J K : Type} [Fintype I] [Fintype J] [Field K] [NumberField K]
    (a : I → Option J → Kˣ) (c : K) (p : Polynomial K) (hp : p ≠ 0) (root : p.IsRoot c)
    (D m : ℕ) (forms : ∀ j : Fin (p.natDegree+1), ∃ G : MvPolynomial (RatioParameters I J) ℤ,
      G.totalDegree ≤ D ∧ coefficientSum G ≤ 2^m ∧ p.coeff j.val = aeval (ratioParameterValues a) G) :
    weilHeight c ≤ (m:ℝ) + log 2 + 2 * (D:ℝ) * ∑ z : I × Option J, weilHeight (a z.1 z.2 : K) := by
  classical
  choose g dG sG rep using forms
  let x := ratioParameterValues a
  let F := (optionEquivLeft ℤ (RatioParameters I J)).symm (assemble g)
  have eF : optionEquivLeft ℤ (RatioParameters I J) F = assemble g := AlgEquiv.apply_symm_apply ..
  have ep : outputPolynomial x (MvPolynomial.map (Int.castRingHom K) F) = p := by
    rw [relation_evaluation, eF]
    ext j
    rw [Polynomial.coeff_map, assemble_coeff]
    split
    next h => exact (rep ⟨j,h⟩).symm
    next h => simp [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < j)]
  have hD : parameterDegree F ≤ D := by
    unfold parameterDegree
    rw [eF]
    apply Finset.sup_le
    intro j _
    rw [assemble_coeff]
    split
    next h => exact dG _
    next h => simp
  have hL : parameterCoefficientSum F ≤ 2^m := by
    unfold parameterCoefficientSum
    rw [eF]
    apply max_le (Nat.pow_pos (by decide : 0 < 2))
    apply Finset.sup_le
    intro j _
    rw [assemble_coeff]
    split
    next h => exact sG _
    next h => simp [coefficientSum]
  have h := ratio_height_from_integral_family a c {F} F (mem_singleton_self _)
  change (outputPolynomial x _ ≠ 0 → (outputPolynomial x _).IsRoot c → _) at h
  rw [ep] at h
  have raw := h hp root
  simp only [sup_singleton] at raw
  have lh := log_nat_cap _ _ (Nat.zero_lt_one.trans_le (le_max_left _ _)) hL
  have dh : (parameterDegree F:ℝ) ≤ D := by exact_mod_cast hD
  exact raw.trans (add_le_add (add_le_add lh (le_refl _)) (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left dh (by norm_num)) (sum_nonneg fun i _ => weilHeight_nonneg _)))

private theorem power_height_additive : (2:ℝ)^402 + log 2 ≤ (2:ℝ)^2086 := by
  have htwo : log 2 ≤ 1 := (Real.log_le_sub_one_of_pos (x:=(2:ℝ)) (by norm_num)).trans_eq (by norm_num)
  calc
    _ ≤ (2:ℝ)^402 + (2:ℝ)^402 := add_le_add (le_refl _) (htwo.trans (one_le_pow₀ (by norm_num)))
    _ = (2:ℝ)^403 := by rw [pow_succ (2:ℝ) 402, mul_two]
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by decide : 403 ≤ 2086)

theorem ratio_height_from_bounded_coefficient_forms {I J K : Type} [Fintype I] [Fintype J] [Field K] [NumberField K]
    (a : I → Option J → Kˣ) (c : K) (p : Polynomial K) (hp : p ≠ 0) (root : p.IsRoot c)
    (forms : ∀ j : Fin (p.natDegree+1), ∃ G : MvPolynomial (RatioParameters I J) ℤ,
      G.totalDegree ≤ 2^112 ∧ coefficientSum G ≤ 2^(2^402) ∧ p.coeff j.val = aeval (ratioParameterValues a) G) :
    weilHeight c ≤ (2:ℝ)^2086+(2:ℝ)^113*∑ z : I × Option J, weilHeight (a z.1 z.2 : K) := by
  have h := ratio_height_from_coefficient_forms a c p hp root (2^112) (2^402) forms
  simp only [Nat.cast_pow, Nat.cast_ofNat] at h
  have slope : (2:ℝ)*2^112 = 2^113 := by rw [pow_succ (2:ℝ) 112, mul_comm]
  rw [slope] at h
  exact h.trans (add_le_add power_height_additive (le_refl _))

end
end PlanarUnitDistances.TorusCritical
