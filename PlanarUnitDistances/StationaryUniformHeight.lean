import PlanarUnitDistances.IntegralCoefficientHomogenization
import PlanarUnitDistances.TorusParameterEliminants

namespace PlanarUnitDistances.TorusCritical
open Finset MvPolynomial Real Height NumberField ArithmeticIntersection EliminantHeight
open scoped Classical
noncomputable section

private theorem affine_height_le_sum {A K : Type*} [Fintype A] [Field K] [NumberField K] (x : A → K) :
    logHeight (fun j : Option A => j.elim 1 x) / Module.finrank ℚ K ≤ ∑ i,weilHeight (x i) := by
  let b (i : A) := ![(1:K),x i]
  let B (t : A → Fin 2) := ∏ i, b i (t i)
  let w (o : Option A) (i : A) : Fin 2 := if o=some i then 1 else 0
  have eq : (fun j : Option A => j.elim 1 x)=B ∘ w := by
    funext j
    cases j with
    | none => simp [B,w,b]
    | some j =>
      change x j = ∏ i,b i (w (some j) i)
      calc x j = ∏ i,if j=i then x i else 1 := by simp
           _ = _ := by
             apply prod_congr rfl
             intro i _
             by_cases h : j=i <;> simp [w,b,h]
  have nz (i : A) : b i ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  have bh : logHeight B = ∑ i,logHeight₁ (x i) := by
    change logHeight (fun t : A → Fin 2 => ∏ i, b i (t i)) = _
    rw [logHeight_fun_prod_eq nz]
    apply sum_congr rfl; intro i _
    exact (logHeight_swap 1 (x i)).trans (logHeight₁_eq_logHeight _).symm
  rw [eq]
  have h := (logHeight_comp_le w B).trans bh.le
  simpa only [weilHeight,sum_div] using div_le_div_of_nonneg_right h (Nat.cast_nonneg (Module.finrank ℚ K))

private theorem ratio_parameter_height {I J K : Type*} [Fintype I] [Fintype J] [Field K] [NumberField K]
    (a : I → Option J → Kˣ) :
    logHeight (fun t : Option (RatioParameters I J) => t.elim 1 (ratioParameterValues a)) / Module.finrank ℚ K ≤
      2*∑ z : I×Option J,weilHeight (a z.1 z.2:K) := by
  apply (affine_height_le_sum (ratioParameterValues a)).trans_eq
  simp [RatioParameters,Fintype.sum_prod_type,ratioParameterValues,weilHeight_inv,two_mul,
    Finset.sum_add_distrib,add_left_comm,add_comm]

private theorem integral_evaluation {K A : Type*} [Field K] [NumberField K] (a : A → K)
    (F : MvPolynomial (Option A) ℤ) :
    outputPolynomial a (MvPolynomial.map (Int.castRingHom K) F) =
      Polynomial.map (aeval (R:=ℤ) a).toRingHom (optionEquivLeft ℤ A F) := by
  induction F using MvPolynomial.induction_on with
  | C r => simp [outputPolynomial]
  | add p q hp hq => simp only [map_add,Polynomial.map_add,hp,hq]
  | mul_X p j hp =>
    simp only [map_mul,MvPolynomial.map_X,Polynomial.map_mul,hp]
    cases j <;> simp [outputPolynomial]

/-- Maximum total parameter degree of the coefficients of the output indeterminate. -/
def parameterDegree {A : Type*} (F : MvPolynomial (Option A) ℤ) : ℕ :=
  let f := optionEquivLeft ℤ A F
  univ.sup (fun j : Fin (f.natDegree+1) => (f.coeff j.val).totalDegree)

/-- Maximum of one and the integer coefficient one-norms of the original
parameter polynomials multiplying each power of the output indeterminate. -/
def parameterCoefficientSum {A : Type*} (F : MvPolynomial (Option A) ℤ) : ℕ :=
  let f := optionEquivLeft ℤ A F
  max 1 (univ.sup (fun j : Fin (f.natDegree+1) => coefficientSum (f.coeff j.val)))

/-- The estimate uses the actual integral coefficient lists before specialization.
The output polynomial can lose arbitrary degree at the parameter tuple. -/
theorem integral_relation_height {A : Type} [Fintype A] (F : MvPolynomial (Option A) ℤ)
    (K : Type) [Field K] [NumberField K] (a : A → K) (c : K) :
      let p := outputPolynomial a (MvPolynomial.map (Int.castRingHom K) F)
      p≠0 → p.IsRoot c →
      weilHeight c ≤ log (parameterCoefficientSum F) + parameterDegree F *
        (logHeight (fun j : Option A => j.elim 1 a) / Module.finrank ℚ K) + log 2 := by
  let f := optionEquivLeft ℤ A F
  let J := Fin (f.natDegree+1)
  let D := parameterDegree F
  let G (j : J) := homogeneousCoefficient D (f.coeff j.val)
  let M := parameterCoefficientSum F
  have pos : 1≤M := le_max_left _ _
  intro p nz root
  let x := fun j : Option A => j.elim 1 a
  have degree (j : J) : (f.coeff j.val).totalDegree ≤ D :=
    le_sup (f:=fun u : J => (f.coeff u.val).totalDegree) (mem_univ j)
  have hsize (j : J) : coefficientSum (G j) ≤ M := by
    change coefficientSum (homogeneousCoefficient D (f.coeff j.val)) ≤ M
    rw [homogeneousCoefficient_size]
    exact (le_sup (f:=fun j : J => coefficientSum (f.coeff j.val)) (mem_univ j)).trans (le_max_right _ _)
  have bound := integral_specialization G pos hsize
    (fun j => (homogeneousCoefficient_degree _ (degree j)).map (Int.castRingHom K)) x
  have rep : p = f.map (aeval (R:=ℤ) a).toRingHom := integral_evaluation a F
  let ι (i : Fin (p.natDegree+1)) : J := ⟨i,Nat.lt_succ_of_le ((Nat.le_of_lt_succ i.isLt).trans
    (by rw [rep]; exact Polynomial.natDegree_map_le))⟩
  let y (j : J) := eval x (MvPolynomial.map (Int.castRingHom K) (G j))
  have coef (n : ℕ) : p.coeff n = eval x
      (MvPolynomial.map (Int.castRingHom K) (homogeneousCoefficient D (f.coeff n))) := by
    rw [rep,Polynomial.coeff_map,eval_map]
    exact (homogeneousCoefficient_aeval D _ a).symm
  have eq : coefficients p = y ∘ ι := by
    funext i
    exact coef i.val
  have projective : coefficientHeight p ≤ logHeight y / Module.finrank ℚ K := by
    unfold coefficientHeight
    rw [eq]
    exact div_le_div_of_nonneg_right (logHeight_comp_le ι y) (Nat.cast_nonneg _)
  exact (weilHeight_root_le p nz root).trans (add_le_add (projective.trans bound) (le_refl _))

/-- For the parameters consisting of each original unit and its inverse,
the slope is twice the parameter degree. -/
theorem ratio_height_from_integral_family {I J K : Type} [Fintype I] [Fintype J]
    [Field K] [NumberField K] (a : I → Option J → Kˣ) (c : K)
    (T : Finset (MvPolynomial (Option (RatioParameters I J)) ℤ))
    (F : MvPolynomial (Option (RatioParameters I J)) ℤ) (hF : F ∈ T) :
    let p := outputPolynomial (ratioParameterValues a) (MvPolynomial.map (Int.castRingHom K) F)
    p≠0 → p.IsRoot c →
    weilHeight c ≤ log (T.sup parameterCoefficientSum : ℕ)+log 2 +
      2*(T.sup parameterDegree : ℕ)*∑ z : I×Option J,weilHeight (a z.1 z.2:K) := by
  intro p nz root
  have est := integral_relation_height F K (ratioParameterValues a) c nz root
  have pos : 1 ≤ parameterCoefficientSum F := le_max_left _ _
  have lh : log (parameterCoefficientSum F) ≤ log (T.sup parameterCoefficientSum : ℕ) := Real.log_le_log
    (by exact_mod_cast (pos : 0 < parameterCoefficientSum F)) (by exact_mod_cast le_sup (f:=parameterCoefficientSum) hF)
  have d : (parameterDegree F:ℝ) ≤ (T.sup parameterDegree:ℕ) := by exact_mod_cast le_sup (f:=parameterDegree) hF
  have hm := mul_le_mul_of_nonneg_left (ratio_parameter_height a) (Nat.cast_nonneg (parameterDegree F))
  have hd := mul_le_mul_of_nonneg_right d
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Finset.sum_nonneg
      (s:=univ) (fun (z : I × Option J) _ => weilHeight_nonneg ((a z.1 z.2):K))))
  linarith only [est,lh,hm,hd]


end
end PlanarUnitDistances.TorusCritical
