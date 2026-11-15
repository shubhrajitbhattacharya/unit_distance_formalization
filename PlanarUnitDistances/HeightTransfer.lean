import PlanarUnitDistances.Heights
import PlanarUnitDistances.HeightMesh

namespace PlanarUnitDistances
namespace HeightTransfer
open Finset Real NumberField OAI.PlanarUnitDistances.LocalHeightTransfer
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

private lemma finite_log_support (x : K) :
    (fun v : FinitePlace K => log⁺ (v x)).HasFiniteSupport := by
  by_cases hx : x = 0
  · subst x
    simp [Function.HasFiniteSupport, Function.support]
  · apply (FinitePlace.hasFiniteMulSupport hx).subset
    intro v hv
    change v x ≠ 1
    change log⁺ (v x) ≠ 0 at hv
    intro he
    exact hv (by simp [he])

private lemma weighted_finite_support {A : Type*} [Fintype A] (w : A → ℝ) (x : A → K) :
    Function.HasFiniteSupport (fun v : FinitePlace K => ∑ a, w a * log⁺ (v (x a))) :=
  Function.HasFiniteSupport.sum (fun a => (finite_log_support (x a)).mul_right (fun _ => w a)) univ

/-- A finite expectation of the absolute height split into expectations at all places. -/
theorem weighted_height_identity {A : Type*} [Fintype A] (w : A → ℝ) (x : A → K) :
    (∑ a, w a * weilHeight (x a)) =
      ((∑ v : InfinitePlace K, (v.mult : ℝ) * ∑ a, w a * log⁺ (v (x a))) +
       (∑ᶠ v : FinitePlace K, ∑ a, w a * log⁺ (v (x a)))) / (Module.finrank ℚ K : ℝ) := by
  classical
  have ha : (∑ v : InfinitePlace K, (v.mult : ℝ) * ∑ a, w a * log⁺ (v (x a))) =
      ∑ a, w a * ∑ v : InfinitePlace K, (v.mult : ℝ) * log⁺ (v (x a)) := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro v _
    ring
  have hf : (∑ᶠ v : FinitePlace K, ∑ a, w a * log⁺ (v (x a))) =
      ∑ a, w a * ∑ᶠ v : FinitePlace K, log⁺ (v (x a)) := by
    have hi := finsum_sum_comm (α := FinitePlace K) (β := A) (M := ℝ)
      univ (fun v a => w a * log⁺ (v (x a)))
      (fun a _ => (finite_log_support (x a)).mul_right (fun _ => w a))
    rw [hi]
    apply sum_congr rfl
    intro a _
    exact (mul_finsum _ _).symm
  rw [ha,hf,← sum_add_distrib,sum_div]
  apply sum_congr rfl
  intro a _
  rw [← mul_add,mul_div_assoc,weilHeight,NumberField.logHeight₁_eq]

variable {P Q : Type} [Fintype P] [Fintype Q]

/-- The coordinate height-transfer inequality in the manuscript, with coefficient 2C. -/
theorem coordinate_height_transfer {C : ℝ} (hC : 1 ≤ C) {w : P → Q → ℝ}
    (hw : ∀ p q, 0 ≤ w p q) (hs : ∑ p, ∑ q, w p q = 1)
    (hc : LabelControl C w) (U : P ⊕ Q → K) :
    (∑ p, ∑ r, left w p * left w r * weilHeight (U (.inl p) - U (.inl r))) ≤
    2*C*((∑ p, ∑ q, w p q * weilHeight (U (.inl p) - U (.inr q))) + 1) := by
  classical
  let a : P × P → K := fun x => U (.inl x.1)-U (.inl x.2)
  let b : P × Q → K := fun x => U (.inl x.1)-U (.inr x.2)
  let μ : P × P → ℝ := fun x => left w x.1 * left w x.2
  let e : P × Q → ℝ := fun x => w x.1 x.2
  let A : InfinitePlace K → ℝ := fun v => ∑ x, μ x * log⁺ (v (a x))
  let B : InfinitePlace K → ℝ := fun v => ∑ x, e x * log⁺ (v (b x))
  let F : FinitePlace K → ℝ := fun v => ∑ x, μ x * log⁺ (v (a x))
  let G : FinitePlace K → ℝ := fun v => ∑ x, e x * log⁺ (v (b x))
  let k := log (3/2 : ℝ)
  let d : ℝ := Module.finrank ℚ K
  have hp : 0 < d := by dsimp only [d]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have harch (v : InfinitePlace K) : A v ≤ C*(B v+k+1)+k := by
    simpa only [A,B,a,b,μ,e,k,Fintype.sum_prod_type,← map_sub,InfinitePlace.norm_embedding_eq] using
      archimedean_transfer (by linarith : 0 ≤ C) hw hs hc (fun i => v.embedding (U i))
  have hfinite (v : FinitePlace K) : F v ≤ C*G v := by
    simpa only [F,G,a,b,μ,e,Fintype.sum_prod_type,FinitePlace.coe_apply] using
      nonarchimedean_transfer v.val (FinitePlace.add_le v) hc U
  have ha : (∑ v : InfinitePlace K, (v.mult : ℝ) * A v) ≤
      C * (∑ v : InfinitePlace K, (v.mult : ℝ) * B v) + d * (C*(k+1)+k) := by
    calc
      _ ≤ ∑ v : InfinitePlace K, (v.mult : ℝ) * (C*(B v+k+1)+k) :=
        sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (harch v) (by positivity)
      _ = ∑ v : InfinitePlace K, (C*((v.mult : ℝ)*B v) + (v.mult : ℝ)*(C*(k+1)+k)) := by
        apply sum_congr rfl
        intro v _
        ring
      _ = _ := by rw [sum_add_distrib,← mul_sum,← sum_mul,← Nat.cast_sum,InfinitePlace.sum_mult_eq]
  have hf : (∑ᶠ v, F v) ≤ C*∑ᶠ v, G v := by
    have h := finsum_le_finsum' (weighted_finite_support μ a)
      ((weighted_finite_support e b).mul_right (fun _ => C)) hfinite
    simpa only [Pi.mul_apply,← mul_finsum,F,G] using h
  have ht : (∑ x, μ x * weilHeight (a x)) ≤ C*(∑ x, e x * weilHeight (b x)) + (C*(k+1)+k) := by
    rw [weighted_height_identity,weighted_height_identity]
    change ((∑ v : InfinitePlace K, (v.mult : ℝ)*A v)+(∑ᶠ v,F v))/d ≤
      C*(((∑ v : InfinitePlace K, (v.mult : ℝ)*B v)+(∑ᶠ v,G v))/d)+(C*(k+1)+k)
    calc
      _ ≤ (C*(∑ v : InfinitePlace K, (v.mult : ℝ)*B v)+d*(C*(k+1)+k)+C*(∑ᶠ v,G v))/d :=
        div_le_div_of_nonneg_right (add_le_add ha hf) hp.le
      _ = _ := by field_simp; ring
  have hk : k ≤ 1/2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3/2)
    dsimp [k]
    linarith
  have hC0 : 0 ≤ C := by linarith
  have he_nonneg : 0 ≤ ∑ x, e x * weilHeight (b x) :=
    sum_nonneg fun x _ => mul_nonneg (hw _ _) (weilHeight_nonneg _)
  have hend : (∑ x, μ x * weilHeight (a x)) ≤ 2*C*((∑ x, e x * weilHeight (b x))+1) := by
    nlinarith only [ht,mul_le_mul_of_nonneg_left hk hC0,hk,hC,mul_nonneg hC0 he_nonneg]
  simpa only [Fintype.sum_prod_type,a,b,μ,e] using hend

end
end HeightTransfer
end PlanarUnitDistances
