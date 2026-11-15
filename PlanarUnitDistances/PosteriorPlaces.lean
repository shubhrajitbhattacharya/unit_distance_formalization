import PlanarUnitDistances.ShiftConsistency
import PlanarUnitDistances.PosteriorCut

namespace OAI.PlanarUnitDistances.PosteriorPlaces
open Real Finset Set MeasureTheory NumberField GridShift StateConsistency
open scoped Classical
noncomputable section

def score (P Q : ℝ → Prop) (s : ℝ) : ℝ :=
  (if P s then 1 else 0)+(if Q s then 1 else 0)-1

private lemma interval_indicator_int (a b : ℝ) :
    (∫s : ℝ,(Icc a b).indicator (fun _ => (1:ℝ)) s) = max (b-a) 0 := by
  rw [integral_indicator_const _ measurableSet_Icc,Real.volume_real_Icc]
  simp

private lemma interval_indicator_L1 (a b : ℝ) :
    Integrable ((Icc a b).indicator (fun _ : ℝ => (1:ℝ))) :=
  ((continuous_const : Continuous (fun _ : ℝ => (1:ℝ))).integrableOn_Icc).integrable_indicator measurableSet_Icc

/-- One level interval. Matching the two coordinates forces opposite one-sided
inequalities; summing their lengths and subtracting the interval length
handles all relative orderings of the two thresholds. -/
theorem local_bound (P Q : ℝ → Prop) {l u t₁ t₂ c : ℝ}
    (hP : MeasurableSet {s | P s}) (hQ : MeasurableSet {s | Q s})
    (hp : ∀ s, P s → s ≤ t₁+c) (hq : ∀ s, Q s → t₂-c ≤ s)
    (hlu : l ≤ u) (hl : l ≤ t₁) (hu : t₂ ≤ u) (hc : 0 ≤ c) :
    (∫s in Icc l u, score P Q s) ≤ t₁-t₂+2*c := by
  let J := Icc l u
  let a := (Icc l (t₁+c)).indicator (fun _ : ℝ => (1:ℝ))
  let b := (Icc (t₂-c) u).indicator (fun _ : ℝ => (1:ℝ))
  let j := J.indicator (fun _ : ℝ => (1:ℝ))
  have ha : Integrable a := interval_indicator_L1 ..
  have hb : Integrable b := interval_indicator_L1 ..
  have hj : Integrable j := interval_indicator_L1 ..
  have hs : IntegrableOn (score P Q) J := by
    have hm : Measurable (score P Q) :=
      ((Measurable.ite hP measurable_const measurable_const).add
       (Measurable.ite hQ measurable_const measurable_const)).sub measurable_const
    haveI : IsFiniteMeasure (volume.restrict J) := inferInstanceAs (IsFiniteMeasure (volume.restrict (Icc l u)))
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards [] with s
    unfold score
    split_ifs <;> norm_num
  have bound : ∫ s, J.indicator (score P Q) s ≤ ∫ s, a s+b s-j s := by
    apply integral_mono (hs.integrable_indicator measurableSet_Icc) ((ha.add hb).sub hj)
    intro s
    change J.indicator (score P Q) s ≤ a s+b s-j s
    by_cases h : s∈J
    · rw [indicator_of_mem h]
      have h₁ : (if P s then (1:ℝ) else 0) ≤ a s := by
        by_cases p : P s
        · simp [p,a,show s∈Icc l (t₁+c) from ⟨h.1,hp s p⟩]
        · simp [p,a,Set.indicator_apply]; positivity
      have h₂ : (if Q s then (1:ℝ) else 0) ≤ b s := by
        by_cases q : Q s
        · simp [q,b,show s∈Icc (t₂-c) u from ⟨hq s q,h.2⟩]
        · simp [q,b,Set.indicator_apply]; positivity
      simp only [score,j,indicator_of_mem h]
      linarith
    · rw [indicator_of_notMem h]
      simp only [j,indicator_of_notMem h,sub_zero]
      simp only [a,b,Set.indicator_apply]
      split_ifs <;> norm_num
  have subint := integral_sub (ha.add hb) hj
  simp only [Pi.add_apply] at subint
  rw [integral_indicator measurableSet_Icc,subint,integral_add ha hb] at bound
  dsimp only [a,b,j,J] at bound
  rw [interval_indicator_int,interval_indicator_int,interval_indicator_int,
    max_eq_left (by linarith : 0≤t₁+c-l),max_eq_left (by linarith : 0≤u-(t₂-c)),
    max_eq_left (sub_nonneg.mpr hlu)] at bound
  linarith

variable {K : Type*} [Field K] [NumberField K]
def archMatch (v : InfinitePlace K) (u : ℝ×ℝ) (a b : K) (s : ℝ) :=
  gridLabel (exp s) (v.embedding a) u = gridLabel (exp s) (v.embedding b) u
def finiteMatch (v : FinitePlace K) (a b : K) (s : ℝ) := v (a-b) ≤ exp s

omit [NumberField K] in
lemma arch_meas (v : InfinitePlace K) (u : ℝ×ℝ) (a b : K) (f : ℝ → ℝ) (hf : Measurable f) :
    MeasurableSet {s | archMatch v u a b (f s)} := by
  apply measurableSet_eq_fun <;> unfold gridLabel <;> fun_prop

lemma arch_log_bound (v : InfinitePlace K) (u : ℝ×ℝ) {a b : K} (hab : a ≠ b)
    {s : ℝ} (h : archMatch v u a b s) : log (v (a-b)) ≤ s + log (sqrt 2) := by
  have h' := norm_le_sqrt_two_of_same_grid (exp_pos s) h
  rw [← map_sub,v.norm_embedding_eq] at h'
  have hh := log_le_log (v.1.pos (sub_ne_zero.mpr hab)) h'
  rwa [log_mul (by positivity) (exp_pos _).ne',log_exp,add_comm] at hh

theorem infinite_local (v : InfinitePlace K) (u₁ u₂ : ℝ×ℝ) {a b c d : K}
    (hab : a≠b) (hcd : c≠d) {l r : ℝ} (hlr : l≤r)
    (hl : l ≤ -log (v (a-b))) (hr : log (v (c-d)) ≤ r) :
    (∫s in Icc l r, score (fun t => archMatch v u₁ a b (-t)) (archMatch v u₂ c d) s) ≤
      -log (v (a-b))-log (v (c-d))+2*log (sqrt 2) := by
  refine local_bound _ _ (arch_meas v u₁ a b (fun s => -s) measurable_neg)
    (arch_meas v u₂ c d id measurable_id) ?_ ?_ hlr hl hr ?_
  · intro s h; linarith [arch_log_bound v u₁ hab h]
  · intro s h; linarith [arch_log_bound v u₂ hcd h]
  · rw [log_sqrt (by norm_num)]; positivity

theorem finite_local (v : FinitePlace K) {a b c d : K}
    (hab : a≠b) (hcd : c≠d) {l r : ℝ} (hlr : l≤r)
    (hl : l ≤ -log (v (a-b))) (hr : log (v (c-d)) ≤ r) :
    (∫s in Icc l r, score (fun t => finiteMatch v a b (-t)) (finiteMatch v c d) s) ≤
      -log (v (a-b))-log (v (c-d)) := by
  have hn := local_bound (fun t => finiteMatch v a b (-t)) (finiteMatch v c d)
    (c := 0) (t₁ := -log (v (a-b))) (t₂ := log (v (c-d)))
    (measurableSet_le measurable_const (measurable_exp.comp measurable_neg))
    (measurableSet_le measurable_const measurable_exp)
    (fun s h => by have H := log_le_log (v.1.pos (sub_ne_zero.mpr hab)) h; rw [log_exp] at H; change log (v (a-b)) ≤ -s at H; linarith)
    (fun s h => by have H := log_le_log (v.1.pos (sub_ne_zero.mpr hcd)) h; rw [log_exp] at H; change log (v (c-d)) ≤ s at H; linarith)
    hlr hl hr le_rfl
  simpa using hn

/-- All infinite places and any finite prime set carrying the product-formula
support of the pair give an all-level excess agreement of at most log 2.
The shifts and both local interval endpoints may vary with the place. -/
theorem all_places {a b c d : K} (hab : a≠b) (hcd : c≠d)
    (F : Finset (FinitePlace K)) (hsupp : ∀ v : FinitePlace K, v ∉ F → v ((a-b)*(c-d))=1)
    (U V : InfinitePlace K → ℝ×ℝ) (l r : InfinitePlace K → ℝ) (l' r' : FinitePlace K → ℝ)
    (ord : ∀v,l v≤r v) (lo : ∀v,l v≤-log (v (a-b))) (hi : ∀v,log (v (c-d))≤r v)
    (ord' : ∀v∈F,l' v≤r' v) (lo' : ∀v∈F,l' v≤-log (v (a-b))) (hi' : ∀v∈F,log (v (c-d))≤r' v) :
    ((∑ v : InfinitePlace K, (v.mult:ℝ)*(∫s in Icc (l v) (r v),
      score (fun t => archMatch v (U v) a b (-t)) (archMatch v (V v) c d) s))+
      ∑ v∈F, ∫s in Icc (l' v) (r' v),
      score (fun t => finiteMatch v a b (-t)) (finiteMatch v c d) s)/(Module.finrank ℚ K:ℝ) ≤ log 2 := by
  let D := (a-b)*(c-d)
  have hn : D≠0 := mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hcd)
  have ph := congrArg log (prod_abs_eq_one hn)
  have pI (v : InfinitePlace K) : 0 < v D := v.1.pos hn
  have pF (v : FinitePlace K) : 0 < v D := v.1.pos hn
  rw [finprod_eq_prod_of_mulSupport_subset _ (fun i h => by
    by_contra hnot; exact h (hsupp i hnot))] at ph
  have pprodI := Finset.prod_pos (s := (univ : Finset (InfinitePlace K))) (fun v _ => pow_pos (pI v) v.mult)
  have pprodF := Finset.prod_pos (s := F) (fun v _ => pF v)
  rw [log_mul pprodI.ne' pprodF.ne',log_prod (fun v _ => (pow_pos (pI v) v.mult).ne'),
    log_prod (fun v _ => (pF v).ne'),log_one] at ph
  simp only [log_pow] at ph
  have lg (v : AbsoluteValue K ℝ) : log (v D) = log (v (a-b))+log (v (c-d)) := by
    rw [show D=(a-b)*(c-d) from rfl,v.map_mul,log_mul (v.pos (sub_ne_zero.mpr hab)).ne' (v.pos (sub_ne_zero.mpr hcd)).ne']
  have upperI := sum_le_sum (s := (univ : Finset (InfinitePlace K))) fun v _ =>
    mul_le_mul_of_nonneg_left (infinite_local v (U v) (V v) hab hcd (ord v) (lo v) (hi v)) (Nat.cast_nonneg v.mult)
  have upperF := sum_le_sum (s := F) fun v hv => finite_local v hab hcd (ord' v hv) (lo' v hv) (hi' v hv)
  have eqI (v : InfinitePlace K) : -log (v (a-b))-log (v (c-d))+2*log (sqrt 2) =
      -log (v D)+log 2 := by
    have idv : log (v D) = log (v (a-b)) + log (v (c-d)) := lg v.1
    rw [idv, log_sqrt (by norm_num)]; ring
  have eqF (v : FinitePlace K) : -log (v (a-b))-log (v (c-d)) = -log (v D) := by
    have idv : log (v D) = log (v (a-b)) + log (v (c-d)) := lg v.1
    rw [idv]; ring
  simp_rw [eqI,mul_add,mul_neg,Finset.sum_add_distrib,Finset.sum_neg_distrib,←Finset.sum_mul] at upperI
  simp_rw [eqF,Finset.sum_neg_distrib] at upperF
  have hd : (0:ℝ)<Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
  have sm : (∑ v : InfinitePlace K, (v.mult:ℝ))=(Module.finrank ℚ K:ℝ) := by exact_mod_cast InfinitePlace.sum_mult_eq
  rw [sm] at upperI
  apply (div_le_iff₀ hd).mpr
  linarith

end
end OAI.PlanarUnitDistances.PosteriorPlaces
