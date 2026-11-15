import PlanarUnitDistances.EliminantHeight
import Mathlib.NumberTheory.Height.MvPolynomial

/-! The height cost of specializing a family of integral coefficient forms.
The number of parameters and the coefficient field degree do not enter
the normalized additive loss. -/

noncomputable section
namespace PlanarUnitDistances.EliminantHeight
open MvPolynomial Height NumberField Real
open Height.AdmissibleAbsValues
variable {K I J : Type*} [Field K] [NumberField K] [Fintype I] [Fintype J] [Nonempty J]

/-- The sum of the absolute values of the integral coefficients. -/
def coefficientSum (p : MvPolynomial I ℤ) : ℕ :=
  ∑ d ∈ p.support, (p.coeff d).natAbs

private lemma int_abs_le (v : AbsoluteValue K ℝ) (a : ℤ) : v (a:K) ≤ (a.natAbs:ℝ) := by
  have nat_le (n : ℕ) : v (n:K) ≤ (n:ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      exact (v.add_le _ _).trans (by simpa using add_le_add_right ih 1)
  obtain ⟨n,rfl|rfl⟩ := Int.eq_nat_or_neg a <;> simpa using nat_le n

theorem integral_height_bound (p : J → MvPolynomial I ℤ) {L : ℕ}
    (size : ∀ j, coefficientSum (p j) ≤ L) :
    Height.mulHeightBound (fun j => (p j).map (Int.castRingHom K)) ≤ (L:ℝ)^totalWeight K := by
  classical
  let F := fun j => (p j).map (Int.castRingHom K)
  have arch (v : AbsoluteValue K ℝ) (j : J) :
      (AddMonoidAlgebra.coeff (F j)).sum (fun _ c => v c) ≤ (L:ℝ) := by
    change (∑ d ∈ (F j).support, v ((F j).coeff d)) ≤ _
    simp only [F, MvPolynomial.coeff_map,
      MvPolynomial.support_map_of_injective (p j) (f:=Int.castRingHom K) (Int.cast_injective (α:=K)), Int.coe_castRingHom]
    exact (Finset.sum_le_sum fun d _ => int_abs_le v _).trans (by exact_mod_cast size j)
  have ultr (v : nonarchAbsVal (K:=K)) (j : J) :
      max (⨆ d : (F j).support, v.val ((F j).coeff d.val)) 1 = 1 := by
    apply max_eq_right
    by_cases empty : IsEmpty (F j).support
    · letI := empty
      simp
    · haveI : Nonempty (F j).support := not_isEmpty_iff.mp empty
      apply ciSup_le
      intro d
      simp only [F,MvPolynomial.coeff_map,Int.coe_castRingHom]
      exact (isNonarchimedean v.val v.prop).apply_intCast_le_one (by simp) (map_one _) (fun _ => map_neg_eq_map ..)
  rw [Height.mulHeightBound_eq]
  change (archAbsVal.map (fun v : AbsoluteValue K ℝ => ⨆ j,
    (AddMonoidAlgebra.coeff (F j)).sum (fun _ c => v c))).prod *
    (∏ᶠ v : nonarchAbsVal, ⨆ j, max (⨆ d : (F j).support, v.val ((F j).coeff d.val)) 1) ≤ _
  simp only [ultr,ciSup_const,finprod_one,mul_one]
  calc
    _ ≤ (archAbsVal.map (fun _ : AbsoluteValue K ℝ => (L:ℝ))).prod :=
      Multiset.prod_map_le_prod_map₀ _ _
        (fun v _ => Real.iSup_nonneg (fun j => Finset.sum_nonneg (fun _ _ => v.nonneg _)))
        (fun v _ => ciSup_le (arch v))
    _ = _ := by simp [totalWeight]

/-- For homogeneous integral forms of degree d and coefficient sum at most
L, evaluation at a projective tuple costs at most d times its absolute
logarithmic height plus log L. -/
theorem integral_specialization (p : J → MvPolynomial I ℤ) {L d : ℕ} (hL : 1 ≤ L)
    (size : ∀ j, coefficientSum (p j) ≤ L)
    (hom : ∀ j, ((p j).map (Int.castRingHom K)).IsHomogeneous d) (x : I → K) :
    Height.logHeight (fun j => ((p j).map (Int.castRingHom K)).eval x) / Module.finrank ℚ K ≤
      Real.log L + d*(Height.logHeight x / Module.finrank ℚ K) := by
  have cap := integral_height_bound (K:=K) p size
  have one : (1:ℝ) ≤ L := by exact_mod_cast hL
  have logcap := Real.log_le_log (by positivity : 0 < max
    (Height.mulHeightBound (fun j => (p j).map (Int.castRingHom K))) 1)
    (max_le cap (one_le_pow₀ one))
  rw [Real.log_pow,NumberField.totalWeight_eq_finrank] at logcap
  have ht := (Height.logHeight_eval_le hom x).trans (add_le_add logcap (le_refl _))
  have hd : (0:ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  apply (div_le_iff₀ hd).2
  convert ht using 1 <;> field_simp <;> ring

end PlanarUnitDistances.EliminantHeight
