import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Selecting one height scale

The probability space below is any finite set of outcomes with explicit point
masses. In the manuscript the outcomes are ordered triples through a common
center. Dependence between the width and the error is allowed.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PlanarUnitDistances

/-- A positive mean length forces many weighted intervals to contain one common point.
Allowing reversed endpoints represents empty intervals. -/
theorem exists_common_point_of_interval_mass {ι : Type*} [Fintype ι]
    (mass lo hi : ι → ℝ) {L U c : ℝ}
    (hL : 0 ≤ L) (hU : 0 ≤ U) (hc : 0 ≤ c)
    (hl : ∀ i, L ≤ lo i) (hu : ∀ i, hi i ≤ U)
    (hmean : U * c < ∑ i, mass i * max (hi i - lo i) 0) :
    ∃ J ∈ Icc L U, c ≤ ∑ i, if J ∈ Icc (lo i) (hi i) then mass i else 0 := by
  classical
  let f (i : ι) := (Icc (lo i) (hi i)).indicator (fun _ : ℝ => mass i)
  have intI (a b d : ℝ) : Integrable ((Icc a b).indicator (fun _ : ℝ => d)) := by
    exact (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have intf (i : ι) : Integrable (f i) := intI _ _ _
  have value (i : ι) : ∫ x, f i x = mass i * max (hi i - lo i) 0 := by
    simp only [f, integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc,
      smul_eq_mul, mul_comm]
  by_contra! hn
  have pointwise (x : ℝ) :
      ∑ i, f i x ≤ (Icc (0 : ℝ) U).indicator (fun _ => c) x := by
    by_cases hx : x ∈ Icc L U
    · have hx' : x ∈ Icc 0 U := ⟨hL.trans hx.1, hx.2⟩
      rw [indicator_of_mem hx']
      simpa only [f, Set.indicator_apply] using (hn x hx).le
    · have he (i : ι) : x ∉ Icc (lo i) (hi i) :=
        fun hx' => hx ⟨(hl i).trans hx'.1, hx'.2.trans (hu i)⟩
      simp only [f, indicator_of_notMem (he _), Finset.sum_const_zero]
      by_cases hx' : x ∈ Icc 0 U <;> simp [hx', hc]
  have hh := integral_mono (integrable_finsetSum _ (fun i _ => intf i)) (intI 0 U c) pointwise
  rw [integral_finsetSum _ (fun i _ => intf i)] at hh
  simp only [value, integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le hU,
    sub_zero, smul_eq_mul] at hh
  exact hmean.not_ge hh

/-- The scale-selection lemma. Its three moment
hypotheses are the lower bound for twice the exceptional point width and the
previous two tail/error estimates. All numerical tolerances are explicit. -/
theorem exists_height_scale {ι : Type*} [Fintype ι]
    (mass W Z : ι → ℝ) (S ε : ℝ)
    (hS : 0 < S) (hε : 0 < ε)
    (hm : ∀ i, 0 ≤ mass i) (htotal : ∑ i, mass i = 1)
    (hW : ∀ i, 0 ≤ W i) (hZ : ∀ i, 0 ≤ Z i)
    (hmean : 2 * S / 203 < ∑ i, mass i * W i)
    (htail : (∑ i, mass i * (if 8 * S / ε < W i then W i else 0)) ≤
      (2 : ℝ)^14 / 2^144 * S)
    (herr : (∑ i, mass i * Z i) ≤ (2 : ℝ)^12 / 2^144 * S) :
    ∃ J ∈ Icc (S / 500) (8 * S / ε),
      ε / 8000 ≤ ∑ i, if J ≤ W i ∧ W i ≤ 2 * J ∧ Z i ≤ J / (648 * 2^111)
                        then mass i else 0 := by
  classical
  let U := 8 * S / ε
  let L := S / 500
  let D : ℝ := 648 * 2^111
  have hD : 0 < D := by dsimp [D]; positivity
  let lo (i : ι) := max (max (W i / 2) L) (D * Z i)
  let hi (i : ι) := if U < W i then 0 else W i
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hlo (i : ι) : L ≤ lo i := (le_max_right _ _).trans (le_max_left _ _)
  have hhi (i : ι) : hi i ≤ U := by
    dsimp [hi]
    split_ifs with h
    · exact hU
    · exact le_of_not_gt h
  have lower (i : ι) :
      W i / 2 - (if U < W i then W i else 0) / 2 - L - D * Z i ≤
        max (hi i - lo i) 0 := by
    have wz := hW i
    have ez := mul_nonneg hD.le (hZ i)
    dsimp [hi, lo]
    split_ifs with h
    · linarith [le_max_right (0 - max (max (W i / 2) L) (D * Z i)) 0]
    · apply le_trans _ (le_max_left _ _)
      have hmax : max (max (W i / 2) L) (D * Z i) ≤ W i / 2 + L + D * Z i :=
        max_le (max_le (by linarith) (by linarith)) (by linarith)
      linarith
  have totalLower := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => mul_le_mul_of_nonneg_left (lower i) (hm i))
  have repr (i : ι) :
      mass i * (W i / 2 - (if U < W i then W i else 0) / 2 - L - D * Z i) =
        mass i * W i / 2 - mass i * (if U < W i then W i else 0) / 2 -
          mass i * L - D * (mass i * Z i) := by ring
  simp only [repr, Finset.sum_sub_distrib, ← Finset.sum_div,
    ← Finset.sum_mul, ← Finset.mul_sum, htotal, one_mul] at totalLower
  have multError := mul_le_mul_of_nonneg_left herr hD.le
  change (∑ i, mass i * (if U < W i then W i else 0)) ≤ _ at htail
  have budget : U * (ε / 8000) < ∑ i, mass i * max (hi i - lo i) 0 := by
    have prod : U * (ε / 8000) = S / 1000 := by
      dsimp [U]
      field_simp
      ring
    rw [prod]
    dsimp [D] at multError
    dsimp [L] at totalLower
    norm_num1 at multError htail
    linarith
  obtain ⟨J, hJ, hcovered⟩ := exists_common_point_of_interval_mass mass lo hi
    hL.le hU (by positivity) hlo hhi budget
  refine ⟨J, hJ, hcovered.trans (Finset.sum_le_sum fun i _ => ?_)⟩
  by_cases hiJ : J ∈ Icc (lo i) (hi i)
  · have hcap : ¬ U < W i := by
      intro h
      have hjzero : J ≤ 0 := by simpa [hi, h] using hiJ.2
      exact (hL.trans_le hJ.1).not_ge hjzero
    have hw₁ : J ≤ W i := by simpa [hi, hcap] using hiJ.2
    have hw₂ := (le_max_left (W i / 2) L).trans
      ((le_max_left (max (W i / 2) L) (D * Z i)).trans hiJ.1)
    have hz := (le_max_right (max (W i / 2) L) (D * Z i)).trans hiJ.1
    have good : J ≤ W i ∧ W i ≤ 2 * J ∧ Z i ≤ J / D :=
      ⟨hw₁, by linarith, (le_div_iff₀ hD).2 (by linarith)⟩
    change (if J ∈ Icc (lo i) (hi i) then mass i else 0) ≤
      if J ≤ W i ∧ W i ≤ 2 * J ∧ Z i ≤ J / D then mass i else 0
    simp [hiJ, good]
  · simp only [hiJ, if_false]
    split_ifs <;> simp [hm]


/-- If the deterministic two-neighbor bound holds, at most one neighbor of a
point above height `u` can have width plus inconsistency less than `u/6`.
At least half of a uniform neighborhood of size at least two is then eligible. -/
theorem half_neighbors_above_threshold {α : Type*} (s : Finset α)
    (cost : α → ℝ) {pointHeight B₀ u : ℝ} (hsize : 2 ≤ s.card)
    (hu : B₀ ≤ u) (hp : u < pointHeight)
    (hpair : ∀ q ∈ s, ∀ r ∈ s, q ≠ r →
      2 * pointHeight ≤ 3 * (cost q + cost r) + B₀) :
    s.card ≤ 2 * (s.filter (fun q => u / 6 ≤ cost q)).card := by
  classical
  have sparse : (s.filter (fun q => ¬u / 6 ≤ cost q)).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun q hq r hr => ?_
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_filter.mp hq
    obtain ⟨hr₁, hr₂⟩ := Finset.mem_filter.mp hr
    by_contra hqr
    have := hpair q hq₁ r hr₁ hqr
    push Not at hq₂ hr₂
    linarith
  have splitCount := Finset.card_filter_add_card_filter_not (s := s) (p := fun q => u / 6 ≤ cost q)
  omega

/-- Weighted mass of an event on a finite sample space. -/
noncomputable def eventMass {ι : Type*} [Fintype ι] (mass : ι → ℝ) (A : ι → Prop) : ℝ :=
  ∑ i, @ite ℝ (A i) (Classical.propDecidable _) (mass i) 0

/-- Integrating the real-valued, finite tail inequalities.
One can use the edge as the outcome, in which case `P,Q,m` are the two
endpoint heights and the edge inconsistency. The inputs are the pointwise
half-neighborhood consequence and the marginal expansion on these level sets. -/
theorem truncated_point_width {ι : Type*} [Fintype ι]
    (mass P Q m : ι → ℝ) {B₀ α : ℝ} (hB : 0 ≤ B₀)
    (hmass : ∀ i, 0 ≤ mass i) (hQ : ∀ i, 0 ≤ Q i) (hm : ∀ i, 0 ≤ m i)
    (hforce : ∀ u ≥ B₀, eventMass mass (fun i => u < P i) / 2 ≤
      eventMass mass (fun i => u < P i ∧ u / 12 ≤ Q i) +
      eventMass mass (fun i => u / 12 ≤ m i))
    (hexpand : ∀ u ≥ B₀, eventMass mass (fun i => u < P i ∧ u / 12 ≤ Q i) ≤
      α * Real.sqrt (eventMass mass (fun i => u < P i) * eventMass mass (fun i => u / 12 ≤ Q i))) :
    (∑ i, mass i * max (P i - B₀) 0) ≤
      48 * α^2 * (∑ i, mass i * Q i) + 48 * (∑ i, mass i * m i) := by
  classical
  have massNN (A : ι → Prop) : 0 ≤ eventMass mass A := by
    unfold eventMass
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hmass]
  have level (u : ℝ) (hu : B₀ ≤ u) :
      eventMass mass (fun i => u < P i) ≤
        4 * α^2 * eventMass mass (fun i => u / 12 ≤ Q i) +
        4 * eventMass mass (fun i => u / 12 ≤ m i) := by
    have h := (hforce u hu).trans (add_le_add_left (hexpand u hu) _)
    let f := eventMass mass (fun i => u < P i)
    let g := eventMass mass (fun i => u / 12 ≤ Q i)
    change f / 2 ≤ α * Real.sqrt (f * g) + _ at h
    change f ≤ 4 * α^2 * g + _
    have hf : 0 ≤ f := massNN _
    have hg : 0 ≤ g := massNN _
    rw [Real.sqrt_mul hf] at h
    nlinarith only [h, sq_nonneg (Real.sqrt f - 2 * α * Real.sqrt g),
      Real.sq_sqrt hf, congrArg (fun x : ℝ => α^2 * x) (Real.sq_sqrt hg)]
  let f (i : ι) := (Ico B₀ (P i)).indicator (fun _ : ℝ => mass i)
  let g (F : ι → ℝ) (i : ι) := (Icc B₀ (12 * F i)).indicator (fun _ : ℝ => mass i)
  have fi (i : ι) : Integrable (f i) := by
    exact (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const (by simp))
  have gi (F : ι → ℝ) (i : ι) : Integrable (g F i) := by
    exact (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have hpw (u : ℝ) : (∑ i, f i u) ≤ 4 * α^2 * (∑ i, g Q i u) + 4 * (∑ i, g m i u) := by
    by_cases hu : B₀ ≤ u
    · have equival (x : ℝ) : u ≤ 12 * x ↔ u / 12 ≤ x := by constructor <;> intro hh <;> linarith
      simpa only [f, g, Set.indicator_apply, mem_Ico, mem_Icc, hu, true_and, equival,
        eventMass] using level u hu
    · simp [f, g, hu]
  have htotal := integral_mono (integrable_finsetSum _ (fun i _ => fi i))
    (((integrable_finsetSum _ (fun i _ => gi Q i)).const_mul (4 * α^2)).add
      ((integrable_finsetSum _ (fun i _ => gi m i)).const_mul 4)) hpw
  change (∫ x, ∑ i, f i x) ≤ ∫ x, (4 * α^2 * (∑ i, g Q i x) + 4 * (∑ i, g m i x)) at htotal
  rw [integral_add ((integrable_finsetSum Finset.univ (fun i _ => gi Q i)).const_mul (4 * α^2))
      ((integrable_finsetSum Finset.univ (fun i _ => gi m i)).const_mul 4),
    integral_const_mul, integral_const_mul, integral_finsetSum _ (fun i _ => fi i),
    integral_finsetSum _ (fun i _ => gi Q i), integral_finsetSum _ (fun i _ => gi m i)] at htotal
  simp only [f, g, integral_indicator_const _ measurableSet_Ico,
    integral_indicator_const _ measurableSet_Icc, Real.volume_real_Ico, Real.volume_real_Icc,
    smul_eq_mul] at htotal
  have replaceBound (F : ι → ℝ) (hF : ∀ i, 0 ≤ F i) :
      (∑ i, max (12 * F i - B₀) 0 * mass i) ≤ 12 * (∑ i, mass i * F i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc
      _ ≤ (12 * F i) * mass i :=
        mul_le_mul_of_nonneg_right (max_le (by linarith) (by linarith [hF i])) (hmass i)
      _ = _ := by ring
  have hbQ := mul_le_mul_of_nonneg_left (replaceBound Q hQ) (by positivity : 0 ≤ 4 * α^2)
  have hbm := replaceBound m hm
  simp_rw [mul_comm (mass _) (max _ 0)]
  linarith

/-- The second inequality of the tail lemma, for any coupling whose two
endpoint positive parts satisfy the same first-moment bound. -/
theorem truncated_pair_width {ι : Type*} [Fintype ι]
    (mass P R : ι → ℝ) {B₀ T : ℝ} (hmass : ∀ i, 0 ≤ mass i)
    (hp : (∑ i, mass i * max (P i - B₀) 0) ≤ T)
    (hr : (∑ i, mass i * max (R i - B₀) 0) ≤ T) :
    (∑ i, mass i * (if 4 * B₀ < P i + R i then P i + R i else 0)) ≤ 4 * T := by
  classical
  have pointwise (i : ι) :
      (if 4 * B₀ < P i + R i then P i + R i else 0) ≤
        2 * (max (P i - B₀) 0 + max (R i - B₀) 0) := by
    split_ifs with h
    · linarith [le_max_left (P i - B₀) 0, le_max_left (R i - B₀) 0]
    · positivity
  have bound := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => mul_le_mul_of_nonneg_left (pointwise i) (hmass i))
  have distribute (i : ι) : mass i * (2 * (max (P i - B₀) 0 + max (R i - B₀) 0)) =
      2 * (mass i * max (P i - B₀) 0 + mass i * max (R i - B₀) 0) := by ring
  simp only [distribute, ← Finset.mul_sum, Finset.sum_add_distrib] at bound
  linarith


/-- An edge law which is uniform within each point's neighborhood. Giving each
fiber its own per-edge weight also covers the uniform law on the whole graph. -/
theorem edge_mass_above_threshold {P : Type*} [Fintype P] (N : P → Type*)
    [∀ p, Fintype (N p)] (b hP : P → ℝ) (hQ m : (p : P) → N p → ℝ)
    {B₀ u : ℝ} (hu : B₀ ≤ u) (hb : ∀ p, 0 ≤ b p)
    (hdeg : ∀ p, 2 ≤ Fintype.card (N p))
    (hpair : ∀ p q r, q ≠ r → 2 * hP p ≤ 3 * (hQ p q + m p q + (hQ p r + m p r)) + B₀) :
    eventMass (ι := Sigma N) (fun e => b e.1) (fun e => u < hP e.1) / 2 ≤
      eventMass (ι := Sigma N) (fun e => b e.1)
        (fun e => u < hP e.1 ∧ u / 12 ≤ hQ e.1 e.2) +
      eventMass (ι := Sigma N) (fun e => b e.1) (fun e => u / 12 ≤ m e.1 e.2) := by
  classical
  let A (p : P) (q : N p) := u / 6 ≤ hQ p q + m p q
  have fibre (p : P) :
      (∑ _ : N p, if u < hP p then b p else 0) ≤
      2 * (∑ q : N p, ((if u < hP p ∧ u / 12 ≤ hQ p q then b p else 0) +
        (if u / 12 ≤ m p q then b p else 0))) := by
    by_cases hp : u < hP p
    · have hc := half_neighbors_above_threshold (Finset.univ : Finset (N p))
          (fun q => hQ p q + m p q) (hdeg p) hu hp (fun q _ r _ h => hpair p q r h)
      change Fintype.card (N p) ≤ 2 * (Finset.univ.filter (A p)).card at hc
      have hc' : (Fintype.card (N p) : ℝ) ≤ 2 * ((Finset.univ.filter (A p)).card : ℝ) :=
        by exact_mod_cast hc
      have hcount (p' : N p → Prop) :
          ((Finset.univ.filter p').card : ℝ) * b p =
            ∑ q, if p' q then b p else 0 := by
        rw [Finset.natCast_card_filter, Finset.sum_mul]
        exact Finset.sum_congr rfl fun q _ => by split_ifs <;> simp
      have ht := mul_le_mul_of_nonneg_right hc' (hb p)
      rw [mul_assoc, hcount] at ht
      have pointwise (q : N p) :
          (if A p q then b p else 0) ≤ (if u / 12 ≤ hQ p q then b p else 0) +
            (if u / 12 ≤ m p q then b p else 0) := by
        split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ <;> dsimp [A] at * <;> linarith [hb p]
      have hsum := Finset.sum_le_sum (s := Finset.univ) (fun q _ => pointwise q)
      simpa only [hp, true_and, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        using ht.trans (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2))
    · simp only [hp, false_and, if_false, Finset.sum_const_zero, zero_add]
      apply mul_nonneg (by norm_num)
      apply Finset.sum_nonneg
      intro q _
      split_ifs <;> simp [hb]
  have total := Finset.sum_le_sum (s := Finset.univ) (fun p _ => fibre p)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at total
  simp only [eventMass, Fintype.sum_sigma]
  linarith

/-- Tail estimate with the manuscript's exact error budget. The expansion
input is the marginal estimate on the level rectangles, with uniform
coefficient squared at most `16·2⁻¹⁴⁴`. -/
theorem edge_width_tail {P : Type*} [Fintype P] (N : P → Type*)
    [∀ p, Fintype (N p)] (b hP : P → ℝ) (hQ m : (p : P) → N p → ℝ)
    {S B₀ α : ℝ} (hS : 0 < S) (hB : 0 ≤ B₀) (hb : ∀ p, 0 ≤ b p)
    (hq : ∀ p q, 0 ≤ hQ p q) (hm : ∀ p q, 0 ≤ m p q)
    (hdeg : ∀ p, 2 ≤ Fintype.card (N p))
    (hpair : ∀ p q r, q ≠ r → 2 * hP p ≤ 3 * (hQ p q + m p q + (hQ p r + m p r)) + B₀)
    (hexpand : ∀ u ≥ B₀, eventMass (ι := Sigma N) (fun e => b e.1)
        (fun e => u < hP e.1 ∧ u / 12 ≤ hQ e.1 e.2) ≤
      α * Real.sqrt (eventMass (ι := Sigma N) (fun e => b e.1) (fun e => u < hP e.1) *
        eventMass (ι := Sigma N) (fun e => b e.1) (fun e => u / 12 ≤ hQ e.1 e.2)))
    (hα : α ^ 2 ≤ 16 / (2 : ℝ)^144)
    (hY : (∑ e : Sigma N, b e.1 * hQ e.1 e.2) ≤ 4 * S)
    (hM : (∑ e : Sigma N, b e.1 * m e.1 e.2) ≤ 4)
    (hlarge : 192 ≤ S / (2 : ℝ)^144) :
    (∑ e : Sigma N, b e.1 * max (hP e.1 - B₀) 0) ≤ (2 : ℝ)^12 / 2^144 * S := by
  have h := truncated_point_width (ι := Sigma N) (fun e => b e.1) (fun e => hP e.1)
    (fun e => hQ e.1 e.2) (fun e => m e.1 e.2) hB (fun e => hb e.1)
    (fun e => hq ..) (fun e => hm ..) (fun _ hu => edge_mass_above_threshold N b hP hQ m
      hu hb hdeg hpair) hexpand
  have a := mul_le_mul_of_nonneg_left hY (by positivity : 0 ≤ 48 * α^2)
  have d := mul_le_mul_of_nonneg_right hα hS.le
  norm_num1 at hα d hlarge ⊢
  linarith

end PlanarUnitDistances

