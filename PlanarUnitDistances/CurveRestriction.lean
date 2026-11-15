import PlanarUnitDistances.GridCount
import Mathlib.Data.Fintype.CardEmbedding

/-! Counting the edges retained by a common-neighbor restriction. An anchor tuple is an embedding of Fin 4, so the four
vertices are distinct. Degree sums always use the original right side. -/

namespace PlanarUnitDistances.CurveRestriction
open Finset
noncomputable section

variable {P Q : Type*} [Fintype P] [Fintype Q]

/-- The common left neighbors of an ordered quadruple of distinct anchors. -/
def common (N : P → Finset Q) (a : Fin 4 ↪ Q) : Finset P := by
  classical exact univ.filter fun p => ∀ i, a i ∈ N p

private theorem anchor_count [DecidableEq Q] (s : Finset Q) :
    (univ.filter fun a : Fin 4 ↪ Q => ∀ i, a i ∈ s).card = s.card.descFactorial 4 := by
  classical
  let e : {a : Fin 4 ↪ Q // ∀ i, a i ∈ s} ≃ (Fin 4 ↪ s) :=
    { toFun := fun a => ⟨fun i => ⟨a.1 i,a.2 i⟩, fun _ _ h => a.1.injective (congrArg Subtype.val h)⟩
      invFun := fun a => ⟨a.trans (Function.Embedding.subtype _),fun i => (a i).property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _ = Fintype.card {a : Fin 4 ↪ Q // ∀ i, a i ∈ s} := (Fintype.card_subtype _).symm
    _ = Fintype.card (Fin 4 ↪ s) := Fintype.card_congr e
    _ = _ := by simp

theorem common_degree_identity (N : P → Finset Q) :
    (∑ a : Fin 4 ↪ Q, ∑ p ∈ common N a, (N p).card) =
      ∑ p : P, (N p).card * (N p).card.descFactorial 4 := by
  classical
  unfold common
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  rw [← sum_filter (fun a : Fin 4 ↪ Q => ∀ i, a i ∈ N p) (fun _ => (N p).card)]
  simpa only [sum_const, nsmul_eq_mul, anchor_count, Nat.cast_id] using
    (Nat.mul_comm ((N p).card.descFactorial 4) (N p).card)

private theorem falling_four (d : ℕ) (h : 8 ≤ d) :
    (d : ℝ)^4 ≤ 16 * (d.descFactorial 4 : ℝ) := by
  have hd : (8 : ℝ) ≤ d := by exact_mod_cast h
  have h1 : (d:ℝ)/2 ≤ d-1 := by linarith
  have h2 : (d:ℝ)/2 ≤ d-2 := by linarith
  have h3 : (d:ℝ)/2 ≤ d-3 := by linarith
  have half : (0:ℝ) ≤ (d:ℝ)/2 := by positivity
  have hd1 : (0:ℝ) ≤ d-1 := half.trans h1
  have hd2 : (0:ℝ) ≤ d-2 := half.trans h2
  have hd3 : (0:ℝ) ≤ d-3 := half.trans h3
  have bound : ((d:ℝ)/2)^4 ≤ ((d:ℝ)-3)*((d:ℝ)-2)*((d:ℝ)-1)*d := by
    calc
      _ = ((d:ℝ)/2)*((d:ℝ)/2)*((d:ℝ)/2)*((d:ℝ)/2) := by ring
      _ ≤ _ := by gcongr; linarith
  norm_num [Nat.descFactorial, Nat.cast_sub (by omega : 3 ≤ d),
    Nat.cast_sub (by omega : 2 ≤ d), Nat.cast_sub (by omega : 1 ≤ d)]
  linarith

private theorem fifth_moment {n : ℕ} [Nonempty P] (hn : Fintype.card P ≤ n)
    (d : P → ℕ) (dense : 16*n ≤ ∑ i, d i) :
    ((∑ i, d i : ℕ) : ℝ)^5 ≤ 512 * (n:ℝ)^4 *
      ∑ i, ((d i * (d i).descFactorial 4 : ℕ) : ℝ) := by
  classical
  let f (i : P) : ℝ := if 8 ≤ d i then (d i:ℝ) else 0
  have hf : ∀ i, 0 ≤ f i := by intro i; dsimp [f]; split_ifs <;> positivity
  have trimmed : ∑ i, (d i:ℝ) ≤ ∑ i, f i + (8:ℝ)*n := by
    calc
      _ ≤ ∑ i, (f i + 8) := by
        apply sum_le_sum
        intro i _
        dsimp [f]
        split_ifs with h
        · linarith
        · simpa using (show (d i : ℝ) ≤ 8 by exact_mod_cast (show d i ≤ 8 by omega))
      _ ≤ _ := by simp [sum_add_distrib]; exact_mod_cast (by omega : Fintype.card P * 8 ≤ 8*n)
  have hd : (16:ℝ)*n ≤ ∑ i, (d i:ℝ) := by exact_mod_cast dense
  have hmass : ∑ i, (d i:ℝ) ≤ 2 * ∑ i, f i := by linarith
  have hcard : (0:ℝ) < Fintype.card P := by exact_mod_cast Fintype.card_pos
  have jensen := GridCount.pow_expect_le f hf 5
  simp only [Fintype.expect_eq_sum_div_card, div_pow] at jensen
  have power : (∑ i, f i)^5 ≤ (Fintype.card P:ℝ)^4 * (∑ i, f i^5) := by
    field_simp at jensen
    nlinarith [jensen]
  have hweight (i : P) : f i^5 ≤ 16 * ((d i * (d i).descFactorial 4 : ℕ):ℝ) := by
    dsimp [f]
    split_ifs with h
    · rw [Nat.cast_mul, pow_succ]
      calc
        _ ≤ (16 * ((d i).descFactorial 4 : ℝ)) * (d i:ℝ) :=
          mul_le_mul_of_nonneg_right (falling_four (d i) h) (Nat.cast_nonneg _)
        _ = _ := by
          change (16 * ((d i).descFactorial 4 : ℝ)) * (d i:ℝ) =
            16 * ((d i:ℝ) * ((d i).descFactorial 4 : ℝ))
          ac_rfl
    · simp; positivity
  push_cast
  calc
    (∑ i, (d i:ℝ))^5 ≤ (2 * ∑ i, f i)^5 :=
      pow_le_pow_left₀ (by positivity) hmass 5
    _ = 32 * (∑ i, f i)^5 := by ring
    _ ≤ 32 * ((n:ℝ)^4 * ∑ i, f i^5) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact power.trans (by gcongr)
    _ ≤ 32 * ((n:ℝ)^4 * ∑ i, (16 * ((d i * (d i).descFactorial 4 : ℕ):ℝ))) := by
      gcongr with i
      exact hweight i
    _ = _ := by rw [← mul_sum]; push_cast; ring

/-- Under the size and density hypotheses an ordered, distinct right
quadruple has a common neighborhood carrying the stated original edges. -/
theorem four_anchors [Nonempty P] {n : ℕ} (hn : 0 < n)
    (hp : Fintype.card P ≤ n) (hq : Fintype.card Q ≤ n)
    (N : P → Finset Q) (dense : 16*n ≤ ∑ p, (N p).card) :
    ∃ a : Fin 4 ↪ Q, (((∑ p, (N p).card : ℕ):ℝ)^5) / (512 * (n:ℝ)^8) ≤
      (∑ p ∈ common N a, ((N p).card:ℝ)) := by
  classical
  let mass (a : Fin 4 ↪ Q) : ℝ := ∑ p ∈ common N a, ((N p).card:ℝ)
  let e : ℝ := (∑ p, (N p).card : ℕ)
  have he : 0 < e := by dsimp [e]; exact_mod_cast (show 0 < ∑ p, (N p).card by omega)
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hm : e^5 ≤ 512 * (n:ℝ)^4 * ∑ a, mass a := by
    have h := fifth_moment hp (fun p => (N p).card) dense
    have hc := common_degree_identity N
    dsimp [mass, e]
    norm_cast
    exact_mod_cast (show (∑ p, (N p).card)^5 ≤ 512*n^4*(∑ a, ∑ p ∈ common N a, (N p).card) by
      rw [hc]; exact_mod_cast h)
  have nh : (Finset.univ : Finset (Fin 4 ↪ Q)).Nonempty := by
    by_contra! h
    rw [h, sum_empty, mul_zero] at hm
    exact (pow_pos he 5).not_ge hm
  have cardA : Fintype.card (Fin 4 ↪ Q) ≤ n^4 := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin]
    exact (Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left hq _)
  have hsum : ∑ _ : Fin 4 ↪ Q, e^5/(512*(n:ℝ)^8) ≤ ∑ a, mass a := by
    simp only [sum_const, card_univ, nsmul_eq_mul]
    calc
      _ ≤ (n:ℝ)^4 * (e^5/(512*(n:ℝ)^8)) := by gcongr; exact_mod_cast cardA
      _ = e^5 / (512*(n:ℝ)^4) := by field_simp
      _ ≤ _ := (div_le_iff₀ (by positivity)).mpr (by linarith [hm])
  obtain ⟨a,_,ha⟩ := exists_le_of_sum_le nh hsum
  exact ⟨a,ha⟩


/-- The exact constant after the second curve restriction, including the
sixth power of the factor count. -/
theorem second_restriction {e e₁ e₂ n D : ℝ} (he : 0 ≤ e) (hn : 0 < n) (hD : 0 < D)
    (h₁ : e^5 / (512*D*n^8) ≤ e₁) (h₂ : e₁^5 / (512*D*n^8) ≤ e₂) :
    e^25 / ((512*D)^6 * n^48) ≤ e₂ := by
  have h := pow_le_pow_left₀ (by positivity) h₁ 5
  apply le_trans _ h₂
  calc
    _ = (e^5/(512*D*n^8))^5 / (512*D*n^8) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right h (by positivity)

/-- Degree bounds used in the final graph count. -/
def curveDegree : ℝ := 80
def restrictionCost : ℝ := (512 * curveDegree)^6


end
end PlanarUnitDistances.CurveRestriction
