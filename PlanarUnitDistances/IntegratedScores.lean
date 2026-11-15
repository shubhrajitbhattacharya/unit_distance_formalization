import PlanarUnitDistances.FirstComparison

namespace OAI.PlanarUnitDistances.CommonTemplate
open Finset FiniteLaw FiniteStarCoupling CrossSampling CrossStructure StrictCross
open ObservedMembership TemplateCoupling CrossPrediction FiniteMarginalScore
open scoped Classical
noncomputable section
variable {P Q A B H I L T : Type*} [Fintype P] [Fintype Q] [Fintype A] [Fintype B]
  [Fintype H] [Fintype I] [Nonempty I] [Fintype L] [Nonempty L] [Fintype T]

lemma prediction_error_bound (π : Law (P×Q)) (h : P → H) (hp : ∀p,0<(left π).val p)
    (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B) :
    predictionError π h x y ≤ inconsistency π bit x y + 4/(Fintype.card L:ℝ)+
      Real.sqrt 6 * hashNorm (C := L) (right π) (col π) h x := by
  have main := cross_error_same_history (C := L) (right π) (col π) (by rwa [mixture_left]) h x y
  have pp : predictionError π h x y = 1 - predicted (right π) (col π) h x y := by
    unfold predictionError predicted posteriorState crossMass
    rw [mixture_left,avg_sub,avg_const]
    congr 1
    rw [col_avg]
    apply avg_congr; intro pq
    rw [←avg_ite]
    rw [push_avg]
    apply avg_congr; intro p
    unfold Hashing.indicator
    split_ifs <;> simp_all
  have aa : 1-actual (right π) (col π) x y ≤ inconsistency π bit x y := by
    unfold actual inconsistency
    rw [col_avg,←avg_const π 1,←avg_sub]
    unfold event
    apply avg_mono; intro pq
    unfold Hashing.indicator
    by_cases hc : Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2)
    · simp [hc,consistent_adj hc]
    · split_ifs <;> norm_num
  linarith

/-- The finite probability law of the common levels can be any joint law of
measurable vertex labels and bits, including a pushforward from a continuum. -/
structure CommonLevel (P Q A B : Type*) where
  x : P → A×B
  y : Q → A×B
  bit : P → Q → Bool
  deriving Fintype

instance : MeasurableSpace (CommonLevel P Q A B) := ⊤
instance : MeasurableSingletonClass (CommonLevel P Q A B) := ⟨fun _ => trivial⟩

/-- A finite snapshot is measurable once each of its underlying label or bit
maps is measurable. No continuity assumption on the labels is needed. -/
theorem measurable_snapshot {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B] [MeasurableSingletonClass B]
    (t : Ω → CommonLevel P Q A B)
    (h₁ : ∀ p, Measurable (fun j => (t j).x p))
    (h₂ : ∀ q, Measurable (fun j => (t j).y q))
    (h₃ : ∀ p q, Measurable (fun j => (t j).bit p q)) :
    Measurable t := by
  let make (z : (P → A×B) × (Q → A×B) × (P → Q → Bool)) :
      CommonLevel P Q A B := ⟨z.1,z.2.1,z.2.2⟩
  have hh := (measurable_pi_iff.mpr h₁).prodMk
    ((measurable_pi_iff.mpr h₂).prodMk (measurable_pi_iff.mpr (fun p => measurable_pi_iff.mpr (h₃ p))))
  exact (measurable_of_finite make).comp hh

def cvT (π : Law (P×Q)) (h : P → H) (t : CommonLevel P Q A B) :=
  avg (templates π (listLaw (I := I) π h)) (fun θ => VP (slice π (listLaw (I := I) π h) θ) t.bit)
def cdT (π : Law (P×Q)) (h : P → H) (t : CommonLevel P Q A B) :=
  avg (templates π (listLaw (I := I) π h)) (fun θ => DP (slice π (listLaw (I := I) π h) θ) t.bit t.y)
def posteriorMoment (π : Law (P×Q)) (h : P → H) (t : CommonLevel P Q A B) :=
  avg (left π) (fun p => tau (posteriorState π h t.x (h p)))

lemma avg_div (τ : Law T) (f : T → ℝ) (c : ℝ) :
    avg τ (fun t => f t/c) = avg τ f/c := by simp only [div_eq_inv_mul,avg_smul]

def commonInformation (π : Law (P×Q)) :=
  FiniteInformation.KL (FiniteInformation.wedge (right π).val (fun q => (col π q).val))
    (fun pp : P×P => (left π).val pp.1*(left π).val pp.2)

/-- Fix the equality decider at the time the norm is defined. A history realized
as a product has its own decidable-equality instance. -/
def residualNorm (π : Law (P×Q)) (h : P → H) (x : P → A×B) :=
  hashNorm (C := L) (right π) (col π) h x

private lemma residualNorm_eq (π : Law (P×Q)) (h : P → H) (x : P → A×B) (d : DecidableEq H) :
    residualNorm (L := L) π h x =
    @hashNorm P Q H A B L _ _ _ _ _ _ d _ _ _ (right π) (col π) h x := by
  exact congrArg (fun dec : DecidableEq H =>
    @hashNorm P Q H A B L _ _ _ _ _ _ dec _ _ _ (right π) (col π) h x) (Subsingleton.elim _ d)

/-- Average the two one-level inequalities before budgeting the vector residual.
This applies to any level law and any single fixed history. -/
theorem scores_for_history (π : Law (P×Q)) (h : P → H) (hp : ∀p,0<(left π).val p)
    (τ : Law T) (t : T → CommonLevel P Q A B) {ζ u : ℝ} (hζ : 0<ζ) (hu : 0<u) :
    let m := avg τ (fun j => inconsistency π (t j).bit (t j).x (t j).y)
    let e := avg τ (fun j => predictionError π h (t j).x (t j).y)
    let N := avg τ (fun j => residualNorm (L := L) π h (t j).x)
    e ≤ m + 4/(Fintype.card L:ℝ)+Real.sqrt 6*N ∧
    (avg τ (fun j => cvT (I := I) π h (t j))+avg τ (fun j => VQ π (t j).bit))/6 ≤
      avg τ (fun j => cdT (I := I) π h (t j))+avg τ (fun j => DQ π (t j).bit (t j).x) +
      16*(m+e/ζ+16/((Fintype.card I:ℝ)*u^2)+3*(ζ+u)+4/(Fintype.card L:ℝ)+Real.sqrt 2*N) ∧
    avg τ (fun j => VP π (t j).bit)/6 ≤ avg τ (fun j => DP π (t j).bit (t j).y) +
      avg τ (fun j => posteriorMoment π h (t j))+16*(m+e/ζ+ζ) := by
  constructor
  · have hh := avg_mono τ (fun j => prediction_error_bound (L := L) π h hp (t j).bit (t j).x (t j).y)
    simpa only [avg_add,avg_const,avg_smul,residualNorm] using hh
  constructor
  · have hh := avg_mono τ (fun j => first_comparison (I := I) (L := L) π h hp (t j).bit (t j).x (t j).y hζ hu)
    simpa only [avg_div,avg_add,avg_const,avg_smul,cvT,cdT,residualNorm] using hh
  · have hh := avg_mono τ (fun j => marginal_score π h (t j).bit (t j).x (t j).y hζ)
    simpa only [avg_div,avg_add,avg_const,avg_smul,posteriorMoment,inconsistency] using hh

private theorem common_history (π : Law (P×Q)) (τ : Law T)
    (t : T → CommonLevel P Q A B) (K : ℕ) (hK : 0<K) :
    ∃ n<K, ∃ h : P → FiniteInformation.History (L×L) n,
      (univ.image h).card ≤ (Fintype.card L)^(2*(K-1)) ∧
      avg τ (fun j => residualNorm (L := L) π h (t j).x) ≤
        4*Real.sqrt 3*(commonInformation π/(K:ℝ))^(1/4:ℝ) := by
  obtain ⟨n,hn,h,sz,he⟩ := exists_vector_cross_history (C := L) (right π) (col π) τ
    (fun j => (t j).x) K hK
  refine ⟨n,hn,h,sz,?_⟩
  simp_rw [residualNorm_eq (d := FiniteInformation.historyDecidableEq (L×L) n)]
  simpa only [commonInformation,mixture_left] using he

set_option maxHeartbeats 350000 in
theorem integrated_scores (π : Law (P×Q)) (hp : ∀p,0<(left π).val p)
    (τ : Law T) (t : T → CommonLevel P Q A B) (K : ℕ) (hK : 0<K)
    {ζ u : ℝ} (hζ : 0<ζ) (hu : 0<u) :
    let R := (commonInformation π/(K:ℝ))^(1/4:ℝ)
    let m := avg τ (fun j => inconsistency π (t j).bit (t j).x (t j).y)
    let a := m+4/(Fintype.card L:ℝ)+4*Real.sqrt 3*Real.sqrt 6*R
    ∃ n<K, ∃ h : P → FiniteInformation.History (L×L) n,
      (univ.image h).card ≤ (Fintype.card L)^(2*(K-1)) ∧
      avg τ (fun j => predictionError π h (t j).x (t j).y) ≤ a ∧
      (avg τ (fun j => cvT (I := I) π h (t j))+avg τ (fun j => VQ π (t j).bit))/6 ≤
        avg τ (fun j => cdT (I := I) π h (t j))+avg τ (fun j => DQ π (t j).bit (t j).x) +
        16*(m+a/ζ+16/((Fintype.card I:ℝ)*u^2)+3*(ζ+u)+4/(Fintype.card L:ℝ)+4*Real.sqrt 6*R) ∧
      avg τ (fun j => VP π (t j).bit)/6 ≤ avg τ (fun j => DP π (t j).bit (t j).y) +
        avg τ (fun j => posteriorMoment π h (t j))+16*(m+a/ζ+ζ) := by
  obtain ⟨n,hn,h,sz,he⟩ := common_history (L := L) π τ t K hK
  let R := (commonInformation π/(K:ℝ))^(1/4:ℝ)
  let m := avg τ (fun j => inconsistency π (t j).bit (t j).x (t j).y)
  let e := avg τ (fun j => predictionError π h (t j).x (t j).y)
  let a := m+4/(Fintype.card L:ℝ)+4*Real.sqrt 3*Real.sqrt 6*R
  let N := avg τ (fun j => residualNorm (L := L) π h (t j).x)
  change N ≤ 4*Real.sqrt 3*R at he
  have mul6 := mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg 6)
  have mul2 := mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg 2)
  have id6 : Real.sqrt 2*Real.sqrt 3 = Real.sqrt 6 := by rw [←Real.sqrt_mul (by norm_num)]; norm_num
  have m6 : Real.sqrt 6*N ≤ 4*Real.sqrt 3*Real.sqrt 6*R := mul6.trans_eq (by ring)
  have m2 : Real.sqrt 2*N ≤ 4*Real.sqrt 6*R := mul2.trans_eq (by rw [←id6]; ring)
  obtain ⟨pe,one,two⟩ := scores_for_history (I := I) (L := L) π h hp τ t hζ hu
  change e ≤ m+4/(Fintype.card L:ℝ)+Real.sqrt 6*N at pe
  have ea : e≤a := pe.trans (add_le_add_right m6 _)
  have ez : e/ζ≤a/ζ := div_le_div_of_nonneg_right ea hζ.le
  have mult (d₁ d₂ c z : ℝ) (hv₁ : d₁≤d₂) (hv₂ : c≤z) :
      16*(m+d₁+16/((Fintype.card I:ℝ)*u^2)+3*(ζ+u)+4/(Fintype.card L:ℝ)+c) ≤
      16*(m+d₂+16/((Fintype.card I:ℝ)*u^2)+3*(ζ+u)+4/(Fintype.card L:ℝ)+z) := by linarith only [hv₁,hv₂]
  refine ⟨n,hn,h,sz,ea,one.trans (add_le_add_right (mult _ _ _ _ ez m2) _),
    two.trans (add_le_add_right ?_ _)⟩
  change 16*(m+e/ζ+ζ)≤16*(m+a/ζ+ζ)
  linarith only [ez]

open MeasureTheory
/-- Normalized level average with respect to a specified finite measure. -/
def levelMean {Ω : Type*} [MeasurableSpace Ω] (σ : Measure Ω) (f : Ω → ℝ) :=
  (∫t, f t ∂σ) / σ.real Set.univ

/-- Both common-level comparisons for the same history, on a genuine measured
continuum of levels. The predicates defining its label and bit arrays are
assumed measurable, and all subsequent finite tests are measurable automatically. -/
theorem continuum_scores {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B] [MeasurableSingletonClass B]
    (π : Law (P×Q)) (hp : ∀p,0<(left π).val p)
    (σ : Measure Ω) [IsFiniteMeasure σ] (hσ : 0<σ.real Set.univ)
    (t : Ω → CommonLevel P Q A B) (h₁ : ∀p,Measurable (fun j => (t j).x p))
    (h₂ : ∀q,Measurable (fun j => (t j).y q)) (h₃ : ∀p q,Measurable (fun j => (t j).bit p q))
    (K : ℕ) (hK : 0<K) {ζ u : ℝ} (hζ : 0<ζ) (hu : 0<u) :
    let R := (commonInformation π/(K:ℝ))^(1/4:ℝ)
    let m := levelMean σ (fun j => inconsistency π (t j).bit (t j).x (t j).y)
    let a := m+4/(Fintype.card L:ℝ)+4*Real.sqrt 3*Real.sqrt 6*R
    ∃ n<K, ∃ h : P → FiniteInformation.History (L×L) n,
      (univ.image h).card ≤ (Fintype.card L)^(2*(K-1)) ∧
      levelMean σ (fun j => predictionError π h (t j).x (t j).y) ≤ a ∧
      (levelMean σ (fun j => cvT (I := I) π h (t j))+levelMean σ (fun j => VQ π (t j).bit))/6 ≤
        levelMean σ (fun j => cdT (I := I) π h (t j))+levelMean σ (fun j => DQ π (t j).bit (t j).x) +
        16*(m+a/ζ+16/((Fintype.card I:ℝ)*u^2)+3*(ζ+u)+4/(Fintype.card L:ℝ)+4*Real.sqrt 6*R) ∧
      levelMean σ (fun j => VP π (t j).bit)/6 ≤ levelMean σ (fun j => DP π (t j).bit (t j).y) +
        levelMean σ (fun j => posteriorMoment π h (t j))+16*(m+a/ζ+ζ) := by
  let ht := measurable_snapshot t h₁ h₂ h₃
  obtain ⟨n,hn,h,sz,pe,A₁,A₂⟩ := integrated_scores (I := I) (L := L) π hp (compress σ hσ t ht) id K hK hζ hu
  refine ⟨n,hn,h,sz,?_,?_,?_⟩
  · simpa only [id_eq,compress_avg,levelMean] using pe
  · simpa only [id_eq,compress_avg,levelMean] using A₁
  · simpa only [id_eq,compress_avg,levelMean] using A₂

end
end OAI.PlanarUnitDistances.CommonTemplate
