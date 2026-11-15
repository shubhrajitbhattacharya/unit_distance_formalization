import PlanarUnitDistances.IntegralGridBound
import PlanarUnitDistances.IntegerCoordinateSplit

namespace PlanarUnitDistances.IntegralGrid
open MvPolynomial EliminantHeight Finset
noncomputable section
variable {U V Z : Type*}

def flatten : InStates U V →+* MvPolynomial (U ⊕ V) ℤ :=
  eval₂Hom (rename Sum.inl).toRingHom (fun v => X (Sum.inr v))

private theorem cost_rename (p : Labels U) (v : U → Z) : coefficientSum (rename v p) ≤ coefficientSum p := by
  have h := coefficientSum_substitution_le p (fun t => (X (v t) : Labels Z))
    (M:=1) (by decide) (fun t => (label_cost _).le)
  rw [rename_eq_aeval, aeval_def, MvPolynomial.algebraMap_eq]
  simpa only [one_pow,mul_one,Function.comp_def] using h

private theorem support_size {p : InStates U V} [Fintype V] (deg : p.totalDegree ≤ 2) :
    p.support.card ≤ 3 ^ Fintype.card V := by
  classical
  have h (d : p.support) (v : V) : d.val v ≤ 2 :=
    (le_degreeOf_of_mem_support v d.prop).trans ((degreeOf_le_totalDegree p v).trans deg)
  let f (d : p.support) (i : V) : Fin 3 := ⟨d.val i,by have := h d i; omega⟩
  have inj : Function.Injective f := by
    intro a b eq
    apply Subtype.ext
    ext i
    exact congrArg Fin.val (congrFun eq i)
  simpa using Fintype.card_le_of_injective f inj

theorem flatten_cost {p : InStates U V} [Fintype V] {n : ℕ} (hb : Bound n p) (deg : p.totalDegree ≤ 2) :
    coefficientSum (flatten p) ≤ 3^Fintype.card V*n := by
  classical
  conv_lhs => rw [p.as_sum,map_sum]
  apply (coefficientSum_sum_le ..).trans
  calc
    _ ≤ ∑ _ ∈ p.support, n := by
      apply sum_le_sum
      intro d _
      simp only [flatten,coe_eval₂Hom,eval₂_monomial]
      apply (coefficientSum_mul_le ..).trans
      have unit : coefficientSum (∏ i ∈ d.support, ((X (.inr i : U ⊕ V) : Labels _) ^ d i)) ≤ 1 := by
        apply (coefficientSum_prod_le ..).trans
        calc
          _ ≤ ∏ _ ∈ d.support, 1 := Finset.prod_le_prod (fun _ _ =>
            (coefficientSum_pow_le ..).trans (by simp [label_cost]))
          _ = 1 := by simp
      change coefficientSum (rename Sum.inl (p.coeff d)) *
        coefficientSum (∏ i ∈ d.support, ((X (.inr i : U ⊕ V) : Labels _) ^ d i)) ≤ n
      simpa only [Nat.mul_one] using Nat.mul_le_mul ((cost_rename _ Sum.inl).trans (hb d).2) unit
    _ ≤ _ := by simpa using Nat.mul_le_mul_right n (support_size deg)

theorem flatten_degree {p : InStates U V} {n : ℕ} (hb : Bound n p) (deg : p.totalDegree ≤ 2) :
    (flatten p).totalDegree ≤ 3 := by
  classical
  conv_lhs => rw [p.as_sum,map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  simp only [flatten,coe_eval₂Hom,eval₂_monomial]
  apply (totalDegree_mul ..).trans
  have h₁ := (totalDegree_rename_le (Sum.inl : U → U ⊕ V) (p.coeff d)).trans (hb d).1
  have h₂ : (∏ i ∈ d.support, (X (.inr i : U ⊕ V) : Labels _) ^ d i).totalDegree ≤ 2 := by
    apply (totalDegree_finsetProd ..).trans
    apply (le_trans _ ((le_totalDegree hd).trans deg))
    apply sum_le_sum
    intro i _
    exact (totalDegree_pow ..).trans (by simp)
  change (rename (Sum.inl : U → U ⊕ V) (p.coeff d)).totalDegree +
    (∏ i ∈ d.support, (X (.inr i : U ⊕ V) : Labels _) ^ d i).totalDegree ≤ 3
  omega

end
end PlanarUnitDistances.IntegralGrid
