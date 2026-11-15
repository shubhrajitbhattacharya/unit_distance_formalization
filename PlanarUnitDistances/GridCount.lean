/- Adapted from OpenAI math, UnitDistances/SmallHeight.lean, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0). Extracted standalone and renamed the namespace. -/
import Mathlib

namespace PlanarUnitDistances.GridCount
open scoped BigOperators
open Finset

lemma pow_expect_le {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (n : ℕ) :
    (𝔼 a, f a)^n ≤ 𝔼 a, (f a)^n := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by positivity
  have h := (convexOn_pow (𝕜 := ℝ) n).map_sum_le
    (t := univ) (w := fun _ : α => (Fintype.card α : ℝ)⁻¹) (p := f)
    (by intros; positivity) (by simp [hc]) (by simpa using hf)
  simpa only [smul_eq_mul, ← Finset.mul_sum, Fintype.expect_eq_sum_div_card,
    div_eq_inv_mul] using h

lemma expect_prod_tuple {α : Type*} [Fintype α] (f : α → ℝ) (n : ℕ) :
    (𝔼 p : Fin n → α, ∏ i, f (p i)) = (𝔼 a, f a)^n := by
  classical
  simp only [Fintype.expect_eq_sum_div_card, ← Fintype.sum_pow,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, div_pow]

theorem complete_grid_density {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (E : α → β → ℝ) (hE : ∀ a b, 0 ≤ E a b)
    (N j : ℕ) :
    (𝔼 a, 𝔼 b, E a b)^(N*j) ≤
      𝔼 p : Fin N → α, 𝔼 r : Fin j → β, ∏ i, ∏ l, E (p i) (r l) := by
  classical
  let X : (Fin N → α) → ℝ := fun p => 𝔼 b, ∏ i, E (p i) b
  have hX : ∀ p, 0 ≤ X p := fun p =>
    Finset.expect_nonneg fun b _ => Finset.prod_nonneg fun i _ => hE (p i) b
  have hEX : (𝔼 a, 𝔼 b, E a b)^N ≤ 𝔼 p, X p := by
    calc
      (𝔼 a, 𝔼 b, E a b)^N = (𝔼 b, 𝔼 a, E a b)^N := by
        rw [Finset.expect_comm]
      _ ≤ 𝔼 b, (𝔼 a, E a b)^N := pow_expect_le _
        (fun b => Finset.expect_nonneg fun a _ => hE a b) N
      _ = 𝔼 b, 𝔼 p : Fin N → α, ∏ i, E (p i) b := by
        apply Finset.expect_congr rfl
        intro b _
        exact (expect_prod_tuple (fun a => E a b) N).symm
      _ = 𝔼 p, X p := by rw [Finset.expect_comm]
  calc
    (𝔼 a, 𝔼 b, E a b)^(N*j) = ((𝔼 a, 𝔼 b, E a b)^N)^j := (pow_mul _ _ _)
    _ ≤ (𝔼 p, X p)^j := pow_le_pow_left₀ (pow_nonneg (Finset.expect_nonneg fun a _ =>
      Finset.expect_nonneg fun b _ => hE a b) N) hEX j
    _ ≤ 𝔼 p, (X p)^j := pow_expect_le X hX j
    _ = 𝔼 p : Fin N → α, 𝔼 r : Fin j → β, ∏ i, ∏ l, E (p i) (r l) := by
      apply Finset.expect_congr rfl
      intro p _
      dsimp only [X]
      rw [← expect_prod_tuple]
      apply Finset.expect_congr rfl
      intro r _
      exact Finset.prod_comm

lemma expect_pair_indicator {α β : Type*} [Fintype α] [Fintype β]
    (E : α → β → Prop) [DecidableRel E] :
    (𝔼 a, 𝔼 b, if E a b then (1 : ℝ) else 0) =
      ((univ.filter fun ab : α × β => E ab.1 ab.2).card : ℝ) /
        ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) := by
  classical
  rw [← Finset.expect_product' univ univ]
  simp only [univ_product_univ, Fintype.expect_eq_sum_div_card,
    Finset.sum_boole, Fintype.card_prod, Nat.cast_mul]

def grids {α β : Type*} [Fintype α] [Fintype β] (E : α → β → Prop)
    [DecidableRel E] (N j : ℕ) : Finset ((Fin N → α) × (Fin j → β)) :=
  univ.filter fun pr => ∀ i l, E (pr.1 i) (pr.2 l)

theorem complete_grid_count {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (E : α → β → Prop) [DecidableRel E] (N j : ℕ) :
    (Fintype.card α : ℝ)^N * (Fintype.card β : ℝ)^j *
      (((univ.filter fun ab : α × β => E ab.1 ab.2).card : ℝ) /
        ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)))^(N*j)
      ≤ (grids E N j).card := by
  classical
  have h := complete_grid_density (fun a b => if E a b then (1 : ℝ) else 0)
    (by intros; split_ifs <;> norm_num) N j
  simp only [Finset.prod_boole, mem_univ, forall_const] at h
  rw [expect_pair_indicator, expect_pair_indicator] at h
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at h
  have hd : 0 < (Fintype.card α : ℝ)^N * (Fintype.card β : ℝ)^j := by positivity
  have hh := (le_div_iff₀ hd).mp h
  simpa only [grids, mul_comm] using hh

end PlanarUnitDistances.GridCount
