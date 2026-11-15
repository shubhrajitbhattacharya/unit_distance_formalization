import PlanarUnitDistances.PosteriorComparison

/-! Dimension-free concentration of the strict-cross probabilities of a list
of independently sampled probability vectors. -/
namespace OAI.PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X J I : Type*} [Fintype X] [Fintype J] [Fintype I]

def independent (μ : Law X) (I : Type*) [Fintype I] : Law (I → X) where
  val x := ∏ i, μ.val (x i)
  nonneg x := prod_nonneg fun i _ => μ.nonneg _
  total := by rw [← Fintype.prod_sum]; simp [μ.total]

lemma avg_sum (μ : Law X) (f : I → X → ℝ) :
    avg μ (fun x => ∑ i, f i x) = ∑ i, avg μ (f i) := by
  simp only [avg, mul_sum]
  rw [sum_comm]

theorem independent_prod (μ : Law X) (f : I → X → ℝ) :
    avg (independent μ I) (fun xs => ∏ i, f i (xs i)) = ∏ i, avg μ (f i) := by
  simp only [independent, avg, ← prod_mul_distrib, Fintype.prod_sum]

lemma independent_single (μ : Law X) (i : I) (f : X → ℝ) :
    avg (independent μ I) (fun xs => f (xs i)) = avg μ f := by
  have h := independent_prod μ (fun j x => if j=i then f x else 1)
  have rhs (j : I) : avg μ (fun x => if j=i then f x else 1) = if j=i then avg μ f else 1 := by
    by_cases he : j=i <;> simp [he,avg_const]
  simpa only [rhs, Finset.prod_ite_eq', Finset.prod_ite_eq, mem_univ,if_true] using h

lemma independent_two (μ : Law X) (i j : I) (hij : i ≠ j) (f g : X → ℝ) :
    avg (independent μ I) (fun xs => f (xs i) * g (xs j)) = avg μ f * avg μ g := by
  let F (k : I) (x : X) := (if k=i then f x else 1)*(if k=j then g x else 1)
  have rhs (k : I) : avg μ (F k) = (if k=i then avg μ f else 1)*(if k=j then avg μ g else 1) := by
    by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [F,avg_const]
  simpa only [rhs, F, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq,mem_univ,if_true]
    using independent_prod μ F

def empiricalError (μ : Law X) (f : X → ℝ) (xs : I → X) : ℝ :=
  (∑ i, f (xs i))/(Fintype.card I:ℝ) - avg μ f

theorem empirical_square (μ : Law X) [Nonempty I] (f : X → ℝ) :
    avg (independent μ I) (fun xs => (empiricalError μ f xs)^2) =
      (avg μ (fun x => (f x)^2) - (avg μ f)^2)/(Fintype.card I:ℝ) := by
  let m := avg μ f
  let g (x : X) := f x-m
  have n : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have mean : avg μ g = 0 := by simp [g,avg_sub,avg_const,m]
  have v : avg μ (fun x => g x*g x) = avg μ (fun x => (f x)^2)-m^2 := by
    have ex (x : X) : g x*g x = (f x)^2- (2*m)*f x + m^2 := by dsimp [g]; ring
    simp only [ex,avg_add,avg_sub,avg_smul,avg_const]
    dsimp [m]
    ring
  have point (xs : I → X) : (empiricalError μ f xs)^2 =
      ((∑ i, ∑ j, g (xs i)*g (xs j)) / (Fintype.card I:ℝ)^2) := by
    rw [← Finset.sum_mul_sum]
    simp only [empiricalError,g,Finset.sum_sub_distrib,Finset.sum_const,card_univ,nsmul_eq_mul,m]
    field_simp
  have diag (i j : I) : avg (independent μ I) (fun xs => g (xs i)*g (xs j)) =
      if i=j then avg μ (fun x => g x*g x) else 0 := by
    by_cases h : i=j
    · subst j; simpa using independent_single μ i (fun x => g x*g x)
    · simp [h,independent_two μ i j h,mean]
  simp only [point, div_eq_inv_mul, avg_smul, avg_sum, diag, Finset.sum_ite_eq, mem_univ, if_true,
    Finset.sum_const,card_univ,nsmul_eq_mul,v]
  dsimp [m]
  field_simp

theorem empirical_vector_square (μ : Law X) [Nonempty I] (v : X → Law J) :
    avg (independent μ I) (fun xs => ∑ a : J, (empiricalError μ (fun x => (v x).val a) xs)^2) ≤
      1/(Fintype.card I:ℝ) := by
  have h (a : J) : avg μ (fun x => ((v x).val a)^2) ≤ avg μ (fun x => (v x).val a) := by
    apply avg_mono
    intro x
    have one : (v x).val a ≤ 1 := (v x).total ▸ single_le_sum (fun j _ => (v x).nonneg j) (mem_univ a)
    nlinarith only [mul_nonneg ((v x).nonneg a) (sub_nonneg.mpr one)]
  rw [avg_sum]
  simp only [empirical_square, ← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ a : J, avg μ (fun x => (v x).val a) :=
      sum_le_sum fun a _ => (sub_le_self _ (sq_nonneg _)).trans (h a)
    _ = 1 := by rw [← avg_sum]; simp only [Law.total,avg_const]

end
end OAI.PlanarUnitDistances.FiniteLaw

namespace OAI.PlanarUnitDistances.CrossSampling
open Finset FiniteLaw StrictCross
open scoped Classical
noncomputable section
variable {X A B I : Type*} [Fintype X] [Fintype A] [Fintype B] [Fintype I] [Nonempty I]

theorem strict_cross_formula (ν : Law (A×B)) (y : A×B) :
    crossMass ν y = (push ν Prod.fst).val y.1 + (push ν Prod.snd).val y.2 - 2*ν.val y := by
  have h (x : A×B) : (if Adj x y then (1:ℝ) else 0) =
      (if x.1=y.1 then 1 else 0)+(if x.2=y.2 then 1 else 0)-2*(if x=y then 1 else 0) := by
    by_cases a : x.1=y.1 <;> by_cases b : x.2=y.2 <;> norm_num [Adj,Prod.ext_iff,a,b]
  have atom : event ν (fun x => x=y) = ν.val y := by
    change fiberMass ν id y = _
    rw [fiberMass_eq]
    simp only [id_eq]
    rw [Finset.sum_eq_single y]
    · simp
    · intro z _ hn; simp [hn]
    · simp
  unfold crossMass event
  simp_rw [h]
  rw [avg_sub, avg_add, avg_smul]
  simp_rw [avg_ite]
  rw [atom]
  rfl

private def vectorError (μ : Law X) {J : Type*} [Fintype J] (v : X → Law J) (xs : I → X) :=
  ∑ a, (empiricalError μ (fun x => (v x).val a) xs)^2

omit [Nonempty I] in
private lemma coordinate_bound (μ : Law X) {J : Type*} [Fintype J] (v : X → Law J) (xs : I → X) (a : J) :
    (empiricalError μ (fun x => (v x).val a) xs)^2 ≤ vectorError μ v xs :=
  Finset.single_le_sum (f := fun j => (empiricalError μ (fun x => (v x).val j) xs)^2)
    (fun _ _ => sq_nonneg _) (mem_univ a)

/-- One event controls all row-column crosses simultaneously, including a
cross subsequently chosen from the observed empirical distribution. -/
theorem empirical_cross_tail (μ : Law X) (v : X → Law (A×B)) {u : ℝ} (hu : 0 < u) :
    event (independent μ I) (fun xs => ∃ y : A×B, u < |empiricalError μ (fun x => crossMass (v x) y) xs|) ≤
      16/((Fintype.card I:ℝ)*u^2) := by
  let a x := push (v x) Prod.fst
  let b x := push (v x) Prod.snd
  let F (xs : I → X) := 4*vectorError μ a xs + 4*vectorError μ b xs + 8*vectorError μ v xs
  have nn (xs : I → X) : 0 ≤ F xs := by
    dsimp [F,vectorError]; positivity
  have point (xs : I → X) (y : A×B) : (empiricalError μ (fun x => crossMass (v x) y) xs)^2 ≤ F xs := by
    let A := empiricalError μ (fun x => (a x).val y.1) xs
    let B := empiricalError μ (fun x => (b x).val y.2) xs
    let C := empiricalError μ (fun x => (v x).val y) xs
    have he : empiricalError μ (fun x => crossMass (v x) y) xs = A+B-2*C := by
      simp only [empiricalError,A,B,C,a,b,strict_cross_formula,Finset.sum_add_distrib,Finset.sum_sub_distrib,
        ← Finset.mul_sum, avg_add,avg_sub,avg_smul]
      ring
    rw [he]
    have hA := coordinate_bound μ a xs y.1
    have hB := coordinate_bound μ b xs y.2
    have hC := coordinate_bound μ v xs y
    change A^2 ≤ _ at hA
    change B^2 ≤ _ at hB
    change C^2 ≤ _ at hC
    dsimp only [F]
    nlinarith only [hA,hB,hC,sq_nonneg (A-B),sq_nonneg (A+C),sq_nonneg (B+C)]
  have sb : avg (independent μ I) F ≤ 16/(Fintype.card I:ℝ) := by
    simp only [F,avg_add,avg_smul]
    have hA := empirical_vector_square (I := I) μ a
    have hB := empirical_vector_square (I := I) μ b
    have hC := empirical_vector_square (I := I) μ v
    change _*avg _ (vectorError μ a) + _*avg _ (vectorError μ b) + _*avg _ (vectorError μ v) ≤ _
    unfold vectorError
    simp only [div_eq_mul_inv,one_mul] at hA hB hC ⊢
    linarith only [hA,hB,hC]
  have sub := event_mono (independent μ I) (P := fun xs => ∃ y : A×B, u < |empiricalError μ (fun x => crossMass (v x) y) xs|)
    (Q := fun xs => u^2 < F xs) (fun xs h => by
      obtain ⟨y,hy⟩ := h
      have hsq := (sq_lt_sq₀ hu.le (abs_nonneg _)).mpr hy
      rw [sq_abs] at hsq
      exact hsq.trans_le (point xs y))
  calc
    _ ≤ avg (independent μ I) F/u^2 := sub.trans (event_markov _ F nn (sq_pos_of_pos hu))
    _ ≤ (16/(Fintype.card I:ℝ))/u^2 := div_le_div_of_nonneg_right sb (sq_nonneg _)
    _ = _ := by ring

end
end OAI.PlanarUnitDistances.CrossSampling
