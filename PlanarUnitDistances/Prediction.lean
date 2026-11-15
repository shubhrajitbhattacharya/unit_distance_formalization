import PlanarUnitDistances.Information

/-! Vector form of manuscript Lemma cb:prediction. The history is exhibited as
the transcript of actual previous tests and can be reused for every pairing.
The independent-test integration follows the proof in OpenAI UnitDistances/Information.lean,
commit adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0), adapted here to a norm. -/

namespace OAI.PlanarUnitDistances.FiniteInformation
open MeasureTheory ProbabilityTheory Finset Real
open scoped InnerProductSpace
noncomputable section
variable {P Q C V : Type*} [Fintype P] [Fintype Q] [Fintype C] [DecidableEq C]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def conditionalResidual {H : Type*} [Fintype H] [DecidableEq H]
    (κ : Q → ℝ) (w : Q → P → ℝ) (h : P → H) (c : P → C) (v : C → V) (q : Q) : V :=
  ∑ p, w q p • (v (c p) - mean (push (marginal κ w) (fun p => (h p,c p))) v (h p))

def predictionNorm {H : Type*} [Fintype H] [DecidableEq H]
    (κ : Q → ℝ) (w : Q → P → ℝ) (h : P → H) (c : P → C) (v : C → V) : ℝ :=
  ∑ q, κ q * ‖conditionalResidual κ w h c v q‖

private lemma unitDirection_inner (x : V) : ⟪x, ‖x‖⁻¹ • x⟫_ℝ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp [norm_ne_zero_iff.mpr hx]

private lemma unitDirection_bound (x : V) : ‖‖x‖⁻¹ • x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  simp [norm_smul, norm_ne_zero_iff.mpr hx]

private lemma frozen_norm_bound (κ : Q → ℝ) (w : Q → P → ℝ)
    (hκ : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p)
    (hsκ : ∑ q, κ q = 1) (hsw : ∀ q, ∑ p, w q p = 1)
    (c : ℕ → P → C) (v : ℕ → C → V)
    {B : ℝ} (hB : 0 ≤ B) (hv : ∀ n x, ‖v n x‖ ≤ B) (K : ℕ) (hK : 0 < K) :
    (∑ n ∈ range K, predictionNorm κ w (transcript c n) (c n) (v n))/(K:ℝ) ≤
      4*B*sqrt (sqrt (KL (wedge κ w)
        (fun pr : P × P => marginal κ w pr.1 * marginal κ w pr.2)/(K:ℝ))) := by
  let a := fun n => conditionalResidual κ w (transcript c n) (c n) (v n)
  let g := fun n q => ‖a n q‖⁻¹ • a n q
  have h := frozen_prediction κ w hκ hw hsκ hsw c v g hB (zero_le_one : (0:ℝ) ≤ 1)
    hv (fun n q => unitDirection_bound _) K hK
  have he (n : ℕ) : discrepancy κ w c v g n = predictionNorm κ w (transcript c n) (c n) (v n) := by
    change |∑ q, κ q * ⟪a n q, ‖a n q‖⁻¹ • a n q⟫_ℝ| = ∑ q, κ q * ‖a n q‖
    simp only [unitDirection_inner]
    exact abs_of_nonneg (sum_nonneg fun q _ => mul_nonneg (hκ q) (norm_nonneg _))
  simpa only [he, mul_one] using h

private lemma predictionNorm_bound {H : Type*} [Fintype H] [DecidableEq H]
    (κ : Q → ℝ) (w : Q → P → ℝ) (hκ : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p)
    (hsκ : ∑ q, κ q = 1) (hsw : ∀ q, ∑ p, w q p = 1)
    (h : P → H) (c : P → C) (v : C → V) {B : ℝ} (hB : 0 ≤ B) (hv : ∀ c, ‖v c‖ ≤ B) :
    ‖predictionNorm κ w h c v‖ ≤ 2*B := by
  let a := conditionalResidual κ w h c v
  let g := fun q => ‖a q‖⁻¹ • a q
  have he : testDiscrepancy κ w h c v g = predictionNorm κ w h c v := by
    change |∑ q, κ q * ⟪a q, ‖a q‖⁻¹ • a q⟫_ℝ| = ∑ q, κ q * ‖a q‖
    simp only [unitDirection_inner]
    exact abs_of_nonneg (sum_nonneg fun q _ => mul_nonneg (hκ q) (norm_nonneg _))
  simpa only [he, mul_one] using testDiscrepancy_bound κ w hκ hw hsκ hsw h c v g hB
    (zero_le_one : (0:ℝ) ≤ 1) hv (fun q => unitDirection_bound _)

variable [MeasurableSpace C]
variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
  {ρ : Measure Ω} {ν : Measure T} [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]

private theorem random_norm_prediction (κ : Q → ℝ) (w : Q → P → ℝ)
    (hκ : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p)
    (hsκ : ∑ q, κ q = 1) (hsw : ∀ q, ∑ p, w q p = 1)
    (tests : ℕ → Ω → T) (ht : ∀ n, Measurable (tests n))
    (hind : iIndepFun tests ρ) (hlaw : ∀ n, ρ.map (tests n) = ν) (t0 : T)
    (c : T → P → C) (v : T → C → V)
    (hc : ∀ p, Measurable (fun t => c t p))
    (hδ : ∀ n, Measurable (fun z : (P → History C n) × T =>
      predictionNorm κ w z.1 (c z.2) (v z.2)))
    {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ t c, ‖v t c‖ ≤ B)
    (K : ℕ) (hK : 0 < K) :
    (∑ n ∈ range K, ∫ ω, ∫ t, predictionNorm κ w
      (transcript (fun k => c (tests k ω)) n) (c t) (v t) ∂ν ∂ρ)/(K:ℝ) ≤
      4*B*sqrt (sqrt (KL (wedge κ w)
        (fun pr : P × P => marginal κ w pr.1 * marginal κ w pr.2)/(K:ℝ))) := by
  let H := fun n ω p => transcript (fun k => c (tests k ω)) n p
  let δ := fun n (z : (P → History C n) × T) =>
    predictionNorm κ w z.1 (c z.2) (v z.2)
  have hH : ∀ n, Measurable (H n) := fun n =>
    measurable_transcript _ (fun k p => (hc p).comp (ht k)) n
  have hb : ∀ n z, ‖δ n z‖ ≤ 2*B := fun n z =>
    predictionNorm_bound κ w hκ hw hsκ hsw z.1 (c z.2) (v z.2) hB (hv z.2)
  have hfresh (n : ℕ) : (∫ ω, δ n (H n ω,tests n ω) ∂ρ) =
      ∫ ω, ∫ t, δ n (H n ω,t) ∂ν ∂ρ :=
    fresh_integral (H n) (tests n) (hH n) (ht n)
      (prefix_independent tests ht hind t0 c hc n) (hlaw n) (δ n) (hδ n) _ (hb n)
  change (∑ n ∈ range K, ∫ ω, ∫ t, δ n (H n ω,t) ∂ν ∂ρ)/(K:ℝ) ≤ _
  simp_rw [← hfresh]
  apply average_integral_bound K hK
  · intro n _
    exact Integrable.of_bound ((hδ n).comp ((hH n).prodMk (ht n))).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω => hb n (H n ω,tests n ω))
  · intro ω
    exact frozen_norm_bound κ w hκ hw hsκ hsw
      (fun n => c (tests n ω)) (fun n => v (tests n ω))
      hB (fun n => hv (tests n ω)) K hK

theorem exists_vector_prediction_history [Nonempty C]
    (κ : Q → ℝ) (w : Q → P → ℝ)
    (hκ : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p)
    (hsκ : ∑ q, κ q = 1) (hsw : ∀ q, ∑ p, w q p = 1)
    (c : T → P → C) (v : T → C → V)
    (hc : ∀ p, Measurable (fun t => c t p))
    (hδ : ∀ n, Measurable (fun z : (P → History C n) × T =>
      predictionNorm κ w z.1 (c z.2) (v z.2)))
    {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ t c, ‖v t c‖ ≤ B)
    (K : ℕ) (hK : 0 < K) :
    ∃ n < K, ∃ tPast : ℕ → T,
      let h := transcript (fun j => c (tPast j)) n
      (univ.image h).card ≤ (Fintype.card C)^(K-1) ∧
      (∫ t, predictionNorm κ w h (c t) (v t) ∂ν) ≤
        4*B*(KL (wedge κ w)
          (fun pr : P × P => marginal κ w pr.1 * marginal κ w pr.2)/(K:ℝ))^(1/4:ℝ) := by
  classical
  let ρ : Measure (ℕ → T) := Measure.infinitePi (fun _ : ℕ => ν)
  let tests := fun n (ω : ℕ → T) => ω n
  have ht : ∀ n, Measurable (tests n) := fun n => measurable_pi_apply n
  have hind : iIndepFun tests ρ := iIndepFun_infinitePi (fun _ => measurable_id)
  have hlaw : ∀ n, ρ.map (tests n) = ν := fun n =>
    (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) n).map_eq
  let t0 : T := Classical.choice (nonempty_of_isProbabilityMeasure ν)
  have hpred := random_norm_prediction κ w hκ hw hsκ hsw tests ht hind hlaw t0 c v hc hδ
    hB hv K hK
  have hD : 0 ≤ KL (wedge κ w) (fun pr : P × P => marginal κ w pr.1 * marginal κ w pr.2) := by
    have hm := marginal_nonneg κ w hκ hw
    have hs := marginal_sum κ w hsκ hsw
    apply KL_nonneg _ _ (wedge_nonneg κ w hκ hw) (fun pr => mul_nonneg (hm _) (hm _))
      (wedge_sum κ w hsκ hsw) _ (wedge_ac κ w hκ hw)
    rw [Fintype.sum_prod_type, ← sum_mul_sum, hs, one_mul]
  rw [sqrt_sqrt_eq_quarter (div_nonneg hD (Nat.cast_nonneg K))] at hpred
  let R := 4*B*(KL (wedge κ w)
    (fun pr : P × P => marginal κ w pr.1 * marginal κ w pr.2)/(K:ℝ))^(1/4:ℝ)
  let H := fun n ω p => transcript (fun k => c (tests k ω)) n p
  let F := fun n (ω : ℕ → T) => ∫ t, predictionNorm κ w (H n ω) (c t) (v t) ∂ν
  have hsum : (∑ n ∈ range K, ∫ ω, F n ω ∂ρ) ≤ ∑ _ ∈ range K, R := by
    have he := (div_le_iff₀ (show (0:ℝ) < K by exact_mod_cast hK)).mp hpred
    simpa only [sum_const, card_range, nsmul_eq_mul, mul_comm, R, F, H] using he
  obtain ⟨n,hn,hnb⟩ := exists_le_of_sum_le (nonempty_range_iff.mpr (Nat.ne_of_gt hK)) hsum
  have hH : Measurable (H n) := measurable_transcript _ (fun k p => (hc p).comp (ht k)) n
  have hpair : Measurable (fun z : (ℕ → T) × T => (H n z.1,z.2)) :=
    (hH.comp measurable_fst).prodMk measurable_snd
  have hi : Integrable (fun z : (ℕ → T) × T =>
      predictionNorm κ w (H n z.1) (c z.2) (v z.2)) (ρ.prod ν) :=
    Integrable.of_bound ((hδ n).comp hpair).aestronglyMeasurable (2*B)
      (Filter.Eventually.of_forall fun z => predictionNorm_bound κ w hκ hw hsκ hsw
        (H n z.1) (c z.2) (v z.2) hB (hv z.2))
  obtain ⟨ω,hω⟩ := exists_le_integral hi.integral_prod_left
  have hn' : n < K := mem_range.mp hn
  refine ⟨n,hn',ω,?_,hω.trans hnb⟩
  calc
    _ ≤ Fintype.card (History C n) := card_le_univ _
    _ = (Fintype.card C)^n := history_card C n
    _ ≤ _ := Nat.pow_le_pow_right Fintype.card_pos (by omega)
end
end OAI.PlanarUnitDistances.FiniteInformation
