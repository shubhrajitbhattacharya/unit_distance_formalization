import PlanarUnitDistances.SparseTest
import PlanarUnitDistances.BoundedHeight

namespace PlanarUnitDistances.BoundedHeight
open Finset Real CircleCells
open OAI.PlanarUnitDistances.FiniteInformation
open scoped Classical BigOperators
noncomputable section

/-- The fresh test is a uniform embedding of the actual coordinate field.
The transcript is chosen for the circle predicates and the given edge law. -/
theorem exists_circle_history {P Q F : Type*} [Fintype P] [Fintype Q] [Field F] [NumberField F]
    (κ : Q → ℝ) (w : Q → P → ℝ) (hk : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p)
    (hsκ : ∑ q, κ q = 1) (hsw : ∀ q, ∑ p, w q p = 1)
    (zp wp : P → F) (zq wq : Q → F) (S : Q → Finset P)
    (hsup : ∀ q p, w q p ≠ 0 → p ∈ S q)
    (hedge : ∀ q p, p ∈ S q → (zp p-zq q)*(wp p-wq q) = 1)
    {a : ℝ} {N L : ℕ} (hN : 0 < N) (hL : 0 < L) :
    ∃ n < L, ∃ hist : P → History (Option (Cell N × Cell N)) n,
      (Finset.univ.image hist).card ≤ (N^4+1)^(L-1) ∧
      1 - (∑ t : F →+* ℂ, ∑ q, κ q * ∑ p, w q p * ∑ r,
        posterior (marginal κ w) hist (hist p) r *
        (if passes (S q) zp wp (zp r) (wp r) (zq q) (wq q) (exp a) N hN t then 1 else 0)) /
        Module.finrank ℚ F ≤
      36*N*(KL (wedge κ w) (fun pr : P×P => marginal κ w pr.1*marginal κ w pr.2)/(L:ℝ))^(1/4:ℝ) := by
  classical
  let Z (t : F →+* ℂ) (p : P) := t (zp p)
  let W (t : F →+* ℂ) (p : P) := t (wp p)
  let flag (t : F →+* ℂ) (q : Q) := exp a < ‖t (zq q)‖ ∨ exp a < ‖t (wq q)‖
  let B t q := accepted (S q) (Z t) (W t) (exp a) N hN
  let c t p := code (exp a) N hN (Z t p) (W t p)
  have card (t : F →+* ℂ) (q : Q) : (B t q).card ≤ 32*N^2+1 := by
    apply accepted_card_le (S q) (Z t) (W t) (t (zq q)) (t (wq q)) (exp_pos a) hN
    intro p hp
    simpa [Z,W] using congrArg t (hedge q p hp)
  have ever (t : F →+* ℂ) (q : Q) (p : P) (hp : w q p ≠ 0) : flag t q ∨ c t p ∈ B t q :=
    Or.inr (code_mem_accepted (S q) (Z t) (W t) (exp a) N hN (hsup q p hp))
  obtain ⟨n,hn,h,hsize,bd⟩ := exists_sparse_test_history κ w hk hw hsκ hsw c flag B N L hN hL card ever
  refine ⟨n,hn,h,?_,?_⟩
  · simpa only [alphabet_card] using hsize
  · have eqv (t : F →+* ℂ) (q : Q) (r : P) : (flag t q ∨ c t r ∈ B t q) ↔
          passes (S q) zp wp (zp r) (wp r) (zq q) (wq q) (exp a) N hN t := by
        simp only [passes, flag, c, B, Z, W, Function.comp_def, or_assoc]
    rw [NumberField.Embeddings.card] at bd
    convert bd using 1
    congr 2
    apply sum_congr rfl
    intro t _
    apply sum_congr rfl
    intro q _
    congr 1
    apply sum_congr rfl
    intro p _
    congr 1
    apply sum_congr rfl
    intro r _
    congr 1
    by_cases ht : flag t q ∨ c t r ∈ B t q
    · rw [if_pos ht, if_pos ((eqv t q r).mp ht)]
    · rw [if_neg ht, if_neg ((eqv t q r).not.mp ht)]

end
end PlanarUnitDistances.BoundedHeight
