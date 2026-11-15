import PlanarUnitDistances.HeightTransfer

namespace PlanarUnitDistances.HeightTransfer
open Finset Real OAI.PlanarUnitDistances.LocalHeightTransfer
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {P Q : Type} [Fintype P] [Fintype Q]

private lemma average_anchor {X : Type*} [Fintype X] (μ f : X → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hs : ∑ x, μ x = 1) : ∃ x, f x ≤ ∑ y, μ y * f y := by
  classical
  have hn : Nonempty X := by
    by_contra! he
    haveI : IsEmpty X := he
    simp at hs
  obtain ⟨x,_,hx⟩ := exists_min_image univ f univ_nonempty
  refine ⟨x, ?_⟩
  calc
    _ = (∑ y, μ y) * f x := by rw [hs,one_mul]
    _ ≤ _ := by
      rw [sum_mul]
      exact sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hx y (mem_univ y)) (hμ y)

/-- A single origin works for both coordinates and for both sides. The point and
center averages below are taken using the two marginals of the same edge law. -/
theorem normalized_four_means {w : P → Q → ℝ} (hw : ∀ p q, 0 ≤ w p q)
    (hs : ∑ p, ∑ q, w p q = 1) (hc : LabelControl 28 w) (Z W : P ⊕ Q → K) {S : ℝ}
    (hz : (∑ p, ∑ q, w p q * weilHeight (Z (.inl p) - Z (.inr q))) ≤ S)
    (hw' : (∑ p, ∑ q, w p q * weilHeight (W (.inl p) - W (.inr q))) ≤ S) :
    ∃ o : P,
      (∑ p, left w p * (weilHeight (Z (.inl p) - Z (.inl o)) +
        weilHeight (W (.inl p) - W (.inl o)))) +
      (∑ q, (∑ p, w p q) * (weilHeight (Z (.inr q) - Z (.inl o)) +
        weilHeight (W (.inr q) - W (.inl o)))) ≤ 226*(S+1) := by
  classical
  let D (x y : P ⊕ Q) :=
    weilHeight (Z x - Z y) + weilHeight (W x - W y)
  have hcZ := coordinate_height_transfer (by norm_num : (1:ℝ) ≤ 28) hw hs hc Z
  have hcW := coordinate_height_transfer (by norm_num : (1:ℝ) ≤ 28) hw hs hc W
  have hp : (∑ o, left w o * ∑ p, left w p * D (.inl p) (.inl o)) ≤ 112*(S+1) := by
    rw [show (∑ o, left w o * ∑ p, left w p * D (.inl p) (.inl o)) =
      ∑ p, ∑ o, left w p * left w o * D (.inl p) (.inl o) by
        simp only [mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro p _
        apply sum_congr rfl
        intro o _
        ring]
    simp only [D,mul_add,sum_add_distrib]
    linarith
  obtain ⟨o, ho⟩ := average_anchor (left w) (fun o => ∑ p, left w p * D (.inl p) (.inl o))
    (left_nonneg hw) hs
  refine ⟨o,?_⟩
  let pt := ∑ p, left w p * D (.inl p) (.inl o)
  have small : pt ≤ 112*(S+1) := ho.trans hp
  have on_edge (p : P) (q : Q) :
      D (.inr q) (.inl o) ≤ D (.inl p) (.inl o) + D (.inl p) (.inr q) + 2*log 2 := by
    have bound (U : P ⊕ Q → K) := weilHeight_sub
      (U (.inl p)-U (.inl o)) (U (.inl p)-U (.inr q))
    have identity (U : P ⊕ Q → K) :
        (U (.inl p)-U (.inl o))-(U (.inl p)-U (.inr q)) = U (.inr q)-U (.inl o) := by ring
    simp only [identity] at bound
    dsimp only [D]
    linarith [bound Z,bound W]
  have hcent : (∑ q, (∑ p, w p q) * D (.inr q) (.inl o)) ≤ pt + 2*S + 2*log 2 := by
    calc
      _ = ∑ p, ∑ q, w p q * D (.inr q) (.inl o) := by simp only [sum_mul]; rw [sum_comm]
      _ ≤ ∑ p, ∑ q, w p q * (D (.inl p) (.inl o) + D (.inl p) (.inr q) + 2*log 2) :=
        sum_le_sum fun p _ => sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (on_edge p q) (hw p q)
      _ = pt + ((∑ p, ∑ q, w p q * weilHeight (Z (.inl p) - Z (.inr q))) +
        (∑ p, ∑ q, w p q * weilHeight (W (.inl p) - W (.inr q)))) + 2*log 2 := by
        simp only [D,pt,left,mul_add,sum_add_distrib,← sum_mul,hs,one_mul]
      _ ≤ _ := by linarith
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  change pt + (∑ q, (∑ p, w p q) * D (.inr q) (.inl o)) ≤ _
  linarith

/-- Rescaling about an edge uses reciprocal scale factors. On the support of the
edge law the second normalized difference is the inverse of the first. -/
theorem edge_scale_normalization {w : P → Q → ℝ} (hw : ∀ p q, 0 ≤ w p q)
    (hs : ∑ p, ∑ q, w p q = 1) (hc : LabelControl 28 w) (Z W : P ⊕ Q → K)
    (unitEdge : ∀ p q, w p q ≠ 0 →
      (Z (.inl p) - Z (.inr q)) * (W (.inl p) - W (.inr q)) = 1)
    {d₀ : K} (hd : d₀ ≠ 0) {S : ℝ}
    (scale : (∑ p, ∑ q, w p q * weilHeight ((Z (.inl p) - Z (.inr q))/d₀)) ≤ S) :
    ∃ o : P,
      let z := fun i : P ⊕ Q => (Z i - Z (.inl o))/d₀
      let u := fun i : P ⊕ Q => d₀*(W i - W (.inl o))
      (∀ p q, w p q ≠ 0 → (z (.inl p)-z (.inr q))*(u (.inl p)-u (.inr q))=1) ∧
      (∑ p, left w p * (weilHeight (z (.inl p)) + weilHeight (u (.inl p)))) +
      (∑ q, (∑ p, w p q) * (weilHeight (z (.inr q)) + weilHeight (u (.inr q)))) ≤
      226*(S+1) := by
  let z := fun i => Z i / d₀
  let u := fun i => d₀ * W i
  have eprod (p q) (h : w p q ≠ 0) :
      (z (.inl p) - z (.inr q))*(u (.inl p) - u (.inr q)) = 1 := by
    dsimp [z,u]
    rw [← sub_div,← mul_sub]
    calc
      _ = (Z (.inl p)-Z (.inr q))*(W (.inl p)-W (.inr q)) := by field_simp
      _ = _ := unitEdge p q h
  have hz : (∑ p, ∑ q, w p q * weilHeight (z (.inl p)-z (.inr q))) ≤ S := by
    simpa only [z,← sub_div] using scale
  have hu : (∑ p, ∑ q, w p q * weilHeight (u (.inl p)-u (.inr q))) ≤ S := by
    refine le_trans (le_of_eq ?_) hz
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro q _
    by_cases h : w p q = 0
    · simp [h]
    · have hi := inv_eq_of_mul_eq_one_right (eprod p q h)
      rw [← hi,weilHeight_inv]
  obtain ⟨o,ho⟩ := normalized_four_means hw hs hc z u hz hu
  refine ⟨o, ?_, ?_⟩
  · intro p q h
    convert eprod p q h using 1
    dsimp only [z,u]
    ring
  · simpa only [z,u,← sub_div,← mul_sub] using ho

end
end PlanarUnitDistances.HeightTransfer
