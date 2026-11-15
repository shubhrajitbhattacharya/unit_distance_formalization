import PlanarUnitDistances.CircleCells
import PlanarUnitDistances.Heights

/-! Relate the actual finite alphabet to the arithmetic residual in the
bounded part of the random-embedding test. -/
noncomputable section
namespace PlanarUnitDistances.CircleCells
open Finset Real

/-- A bounded accepted query has a genuine neighbor in the same pair of
cells. A diameter bound of twice the mesh width suffices in each coordinate. -/
theorem bounded_accepted_residual {ι : Type*} (S : Finset ι) (z w : ι → ℂ)
    {R : ℝ} {N : ℕ} (hR : 0 < R) (hN : 0 < N) (a b c d : ℂ)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (hc : ‖c‖ ≤ R) (hd : ‖d‖ ≤ R)
    (hedge : ∀ i ∈ S, (z i-c)*(w i-d) = 1)
    (haccept : code R N hN a b ∈ accepted S z w R N hN) :
    ‖(a-c)*(b-d)-1‖ ≤ 8 * R * width R N := by
  classical
  rw [code, if_pos ⟨ha,hb⟩, accepted] at haccept
  obtain h | h := mem_insert.mp haccept
  · contradiction
  obtain ⟨t,ht,ht'⟩ := mem_image.mp h
  obtain ⟨i,hi,hpair⟩ := mem_image.mp ht
  obtain ⟨hiS,hz,hw⟩ := mem_filter.mp hi
  have hp := hpair.trans (Option.some.inj ht')
  have hnz := same_cell_near hR hN ha hz (congrArg Prod.fst hp.symm)
  have hnw := same_cell_near hR hN hb hw (congrArg Prod.snd hp.symm)
  have hbd : ‖b-d‖ ≤ 2*R := (norm_sub_le b d).trans (by linarith)
  have hzc : ‖z i-c‖ ≤ 2*R := (norm_sub_le (z i) c).trans (by linarith)
  have he : (a-c)*(b-d)-1 = (a-z i)*(b-d) + (z i-c)*(b-w i) := by
    rw [← hedge i hiS]
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  have h₁ := mul_le_mul hnz hbd (norm_nonneg _) (by unfold width; positivity : 0 ≤ 2 * width R N)
  have h₂ := mul_le_mul hzc hnw (norm_nonneg _) (by positivity : 0 ≤ 2*R)
  nlinarith only [h₁,h₂]

/-- At a *uniform number-field embedding*, for a fixed nonedge, bound the
fraction of embeddings where all four coordinates are bounded and the actual
acceptance test passes. This is the component before averaging a coupling
and adding the probability of overflow. -/
theorem bounded_false_acceptance {K ι : Type*} [Field K] [NumberField K]
    (S : Finset ι) (z w : ι → K) (a b c d : K)
    (hedge : ∀ i ∈ S, (z i-c)*(w i-d) = 1) (hfalse : (a-c)*(b-d)-1 ≠ 0)
    {R s : ℝ} {N : ℕ} (hR : 0 < R) (hs : 0 < s) (hN : 0 < N)
    (hmesh : 8*R*width R N ≤ exp (-s)) :
    let E := univ.filter fun φ : K →+* ℂ =>
      ‖φ a‖ ≤ R ∧ ‖φ b‖ ≤ R ∧ ‖φ c‖ ≤ R ∧ ‖φ d‖ ≤ R ∧
      code R N hN (φ a) (φ b) ∈ accepted S (φ ∘ z) (φ ∘ w) R N hN
    (E.card : ℝ) / (Module.finrank ℚ K : ℝ) ≤ weilHeight ((a-c)*(b-d)-1) / s := by
  classical
  let F := (a-c)*(b-d)-1
  let small := univ.filter fun φ : K →+* ℂ => ‖φ F‖ ≤ exp (-s)
  intro E
  have hsub : E ⊆ small := by
    intro φ hφ
    obtain ⟨_,ha,hb,hc,hd,haccept⟩ := mem_filter.mp hφ
    have hk (i : ι) (hi : i ∈ S) :
        ((φ ∘ z) i-φ c)*((φ ∘ w) i-φ d) = 1 := by
      simpa using congrArg φ (hedge i hi)
    apply mem_filter.mpr ⟨mem_univ _, ?_⟩
    simpa [F] using (bounded_accepted_residual S _ _ hR hN _ _ _ _
      ha hb hc hd hk haccept).trans hmesh
  calc
    _ ≤ (small.card : ℝ) / (Module.finrank ℚ K : ℝ) := by
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card hsub)) (Nat.cast_nonneg _)
    _ ≤ _ := small_embedding_fraction hfalse hs

end PlanarUnitDistances.CircleCells
