import PlanarUnitDistances.LargeScaleExtraction
import PlanarUnitDistances.EventualGraphCounting

namespace PlanarUnitDistances
open OAI.PlanarUnitDistances Filter
open scoped Topology
noncomputable section

/-- The cutoff is universal over all fields and all admissible graphs. -/
def EventualAlgebraicGraphBoundAtScale (minScale : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K] [NumberField K]
    (G : AdmissibleGraph n K), minScale ≤ G.scale → (G.edges.card : ℝ) < (n:ℝ)^(2-1/2000:ℝ)

private theorem eventually_separates {u v b k : ℝ} (huv : u*b < v) (hk : 0 < k) :
    ∀ᶠ t : ℝ in atTop, (2*t^u)^b < k*t^v := by
  have hlarge := (tendsto_rpow_atTop (sub_pos.mpr huv)).eventually_gt_atTop ((2:ℝ)^b / k)
  filter_upwards [hlarge, eventually_gt_atTop (0:ℝ)] with t ht ht0
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg ht0.le _), ← Real.rpow_mul ht0.le]
  have h := (div_lt_iff₀ hk).mp ht
  calc
    (2:ℝ)^b * t^(u*b) < (t^(v-u*b)*k) * t^(u*b) :=
      mul_lt_mul_of_pos_right h (Real.rpow_pos_of_pos ht0 _)
    _ = k*t^v := by
      rw [mul_right_comm, ← Real.rpow_add ht0, sub_add_cancel, mul_comm]

private theorem scale_tends : Tendsto incidenceScale atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : 0 < (1/3:ℝ))).comp tendsto_natCast_atTop_atTop

/-- The lower bound on the extracted edge count forces its vertex parameter past
any fixed graph cutoff. The resulting constant is uniform over real point sets. -/
theorem powerSaving_of_extraction_and_eventual_graph_at_scale {δ minScale : ℝ}
    (hδ : 0 < δ) (hδ' : δ ≤ (2:ℝ)^(-(594036:ℝ)))
    (hextract : DenseGraphExtractionAtScale δ minScale) (hgraph : EventualAlgebraicGraphBoundAtScale minScale) : PowerSaving δ := by
  let g := 3*δ
  let a := 10000*g
  let b : ℝ := 2-1/2000
  have hab : (1+2*a)*b < 2+3*a-180*g := by
    have h := graph_density_exponent hδ'
    dsimp [a,g,b] at *
    linarith
  obtain ⟨k,hk,he⟩ := hextract
  obtain ⟨N₀,hlarge⟩ := eventually_atTop.1 hgraph
  have hv : 0 < 2+3*a-180*g := by
    dsimp [a,g]
    linarith
  have hcut := (tendsto_rpow_atTop hv).eventually_gt_atTop ((N₀:ℝ)^2/k)
  have hsmall : ∀ᶠ n : ℕ in atTop, ∀ X : Finset Plane, X.card = n → AlgebraicPoints X →
      ((orderedPairs X).card : ℝ) < (n:ℝ)^(4/3-δ) := by
    filter_upwards [he, scale_tends.eventually (eventually_separates hab hk), scale_tends.eventually hcut] with n hn hsep hNmass
    intro X hX halg
    by_contra! hcount
    obtain ⟨N,K,f,nf,G,hJ,_,hSize,hLower⟩ := hn X hX halg hcount
    have hthreshold : N₀ ≤ N := by
      by_contra! hNsmall
      have bound : (G.edges.card:ℝ) ≤ (N₀:ℝ)^2 := by
        exact_mod_cast G.edges_card_le_sq.trans (Nat.pow_le_pow_left hNsmall.le 2)
      exact (not_lt_of_ge (hLower.trans bound)) (by
        simpa only [mul_comm k] using (div_lt_iff₀ hk).mp hNmass)
    have hupper := hlarge N hthreshold K G hJ
    have hmon : (N:ℝ)^b ≤ (2*(incidenceScale n)^(1+2*a))^b :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hSize (by norm_num [b])
    exact (not_lt_of_ge hLower) ((hupper.trans_le hmon).trans hsep)
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.1 hsmall
  have hδ1 : δ ≤ 1 := hδ'.trans (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num))
  apply (powerSaving_iff_algebraic δ).mpr
  let C : ℝ := (n₀:ℝ)^2+1
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [sq_nonneg (n₀:ℝ)]
  refine ⟨C, zero_lt_one.trans_le hC, fun X hx ha => ?_⟩
  have hcard : (1:ℝ) ≤ X.card := by exact_mod_cast (by omega : 1 ≤ X.card)
  have hpow := Real.one_le_rpow hcard (by linarith : 0 ≤ 4/3-δ)
  by_cases hn : n₀ ≤ X.card
  · have h := hn₀ X.card hn X rfl ha
    rw [orderedPairs_card, Nat.cast_mul, Nat.cast_ofNat] at h
    have hu : (unitPairCount X : ℝ) ≤ (X.card : ℝ)^(4/3-δ) := by
      linarith [Nat.cast_nonneg (α:=ℝ) (unitPairCount X)]
    exact hu.trans (le_mul_of_one_le_left (by positivity) hC)
  · have hsq : (unitPairCount X : ℝ) ≤ (n₀:ℝ)^2 := by
      exact_mod_cast (unitPairCount_le_card_sq X).trans (Nat.pow_le_pow_left (le_of_not_ge hn) 2)
    exact (hsq.trans (by dsimp [C]; linarith : (n₀:ℝ)^2 ≤ C)).trans
      (le_mul_of_one_le_right (zero_le_one.trans hC) hpow)

/-- It suffices to prove the asymptotic edge bound only on graphs at the selected large scale. -/
theorem theoremA_of_eventual_large_scale_graph
    (hgraph : EventualAlgebraicGraphBoundAtScale ((2:ℝ)^2100/500)) : TheoremA :=
  powerSaving_of_extraction_and_eventual_graph_at_scale exactGap_pos exactGap_lt_largeHeightGap.le
    ProofAssembly.original_extraction_at_large_scale hgraph

end
end PlanarUnitDistances
