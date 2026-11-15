import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-! # Matching finite labels under rectangular expansion

These lemmas use the pushforwards of the vertex counting laws and the edge
law to a common finite label set. Rectangle bounds need only be tested on
individual label classes and their complements.
-/

open scoped BigOperators
open Finset

namespace PlanarUnitDistances

/-- The diagonal estimate, with the exponent written in
terms of the geometric mean of the two counting fractions. -/
theorem dominant_counting_label {ι : Type*} [Fintype ι] [Nonempty ι]
    (u v d : ι → ℝ) {s ξ : ℝ}
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hU : ∑ i, u i = 1) (hV : ∑ i, v i = 1)
    (hξ : 0 ≤ ξ) (hsξ : s + ξ ≤ 1) (hdiag : 1 - s = ∑ i, d i)
    (hcut : ∀ i, d i ≤ Real.sqrt (u i * v i) *
      ((Real.sqrt (u i * v i)) ^ (2 / 25 : ℝ) + ξ)) :
    ∃ i, Real.sqrt ((1 - u i) * (1 - v i)) ≤ (25 / 2 : ℝ) * (s + ξ) := by
  classical
  let x (i : ι) := Real.sqrt (u i * v i)
  let b : ℝ := 2 / 25
  obtain ⟨i, _, hmax⟩ := Finset.univ.exists_max_image x Finset.univ_nonempty
  have hx (j : ι) : 0 ≤ x j := Real.sqrt_nonneg _
  have hsum : ∑ j, x j ≤ 1 := by
    simp only [x, Real.sqrt_mul (hu _)]
    simpa [hU, hV] using Real.sum_sqrt_mul_sqrt_le Finset.univ hu hv
  have hsum' : 1 - s ≤ x i ^ b + ξ := calc
    _ = ∑ j, d j := hdiag
    _ ≤ ∑ j, x j * (x i ^ b + ξ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact (hcut j).trans (mul_le_mul_of_nonneg_left
        (add_le_add_left (Real.rpow_le_rpow (hx j) (hmax j hj) (by norm_num [b])) ξ) (hx j))
    _ = (∑ j, x j) * (x i ^ b + ξ) := Finset.sum_mul .. |>.symm
    _ ≤ x i ^ b + ξ := mul_le_of_le_one_left (add_nonneg (Real.rpow_nonneg (hx i) _) hξ) hsum
  have bern := one_add_mul_self_le_rpow_one_add (s := -(s + ξ)) (by linarith)
    (p := (25 / 2 : ℝ)) (by norm_num)
  have hpow := Real.rpow_le_rpow (show 0 ≤ 1 + -(s + ξ) by linarith)
    (show 1 + -(s + ξ) ≤ x i ^ b by linarith) (show (0 : ℝ) ≤ 25/2 by norm_num)
  rw [← Real.rpow_mul (hx i)] at hpow
  have hb : b * (25/2 : ℝ) = 1 := by norm_num [b]
  rw [hb, Real.rpow_one] at hpow
  have ui : u i ≤ 1 := hU ▸ Finset.single_le_sum (fun j _ => hu j) (Finset.mem_univ i)
  have vi : v i ≤ 1 := hV ▸ Finset.single_le_sum (fun j _ => hv j) (Finset.mem_univ i)
  have amgm (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) : 2 * Real.sqrt (a*c) ≤ a+c := by
    rw [Real.sqrt_mul ha]
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt c), Real.sq_sqrt ha, Real.sq_sqrt hc]
  have hmain := amgm (u i) (v i) (hu i) (hv i)
  change 2 * x i ≤ _ at hmain
  refine ⟨i, ?_⟩
  linarith [amgm (1-u i) (1-v i) (by linarith) (by linarith)]

/-- Small edge-label mismatch implies a single common label with at most twice
the mismatch in total marginal exception mass. Here `h`, `k` are the two
exception masses and `j` is their joint mass. The two lower marginal
bounds together control joint exceptions directly. -/
theorem small_mismatch_dominant_label {ι : Type*} [Fintype ι] [Nonempty ι]
    (u v d h k j : ι → ℝ) {s ξ : ℝ}
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hU : ∑ i, u i = 1) (hV : ∑ i, v i = 1)
    (hξ : 0 ≤ ξ) (hξsmall : ξ ≤ 1 / (2 : ℝ)^100)
    (hs : s ≤ 1 / (2 : ℝ)^52) (hdiag : 1 - s = ∑ i, d i)
    (hcut : ∀ i, d i ≤ Real.sqrt (u i * v i) *
      ((Real.sqrt (u i * v i)) ^ (2 / 25 : ℝ) + ξ))
    (hcomp : ∀ i, j i ≤ Real.sqrt ((1-u i)*(1-v i)) *
      ((Real.sqrt ((1-u i)*(1-v i))) ^ (2 / 25 : ℝ) + ξ))
    (hleft : ∀ i, (27/50 : ℝ)*(1-u i) ≤ h i)
    (hright : ∀ i, (27/50 : ℝ)*(1-v i) ≤ k i)
    (hmismatch : ∀ i, h i + k i - 2 * j i ≤ s) :
    ∃ i, h i + k i ≤ 2*s := by
  have hsum : s + ξ ≤ 1 := by norm_num1 at hξsmall hs; linarith
  obtain ⟨i, hz⟩ := dominant_counting_label u v d hu hv hU hV hξ hsum hdiag hcut
  let z := Real.sqrt ((1-u i)*(1-v i))
  have hzn : 0 ≤ z := Real.sqrt_nonneg _
  change z ≤ _ at hz
  have hz' : z ≤ (1/2 : ℝ) ^ (25 : ℝ) := by
    norm_num1 at hs hξsmall ⊢
    linarith
  have hp := Real.rpow_le_rpow hzn hz' (show (0:ℝ) ≤ 2/25 by norm_num)
  rw [← Real.rpow_mul (by norm_num)] at hp
  norm_num1 at hp
  have hj := hcomp i
  change j i ≤ z * (z ^ (2/25 : ℝ) + ξ) at hj
  have ht : j i ≤ z * (27 / 100 : ℝ) := hj.trans (mul_le_mul_of_nonneg_left (by
    norm_num1 at hξsmall; linarith) hzn)
  have ui : u i ≤ 1 := hU ▸ Finset.single_le_sum (fun l _ => hu l) (Finset.mem_univ i)
  have vi : v i ≤ 1 := hV ▸ Finset.single_le_sum (fun l _ => hv l) (Finset.mem_univ i)
  have hc : 2*z ≤ 1-u i + (1-v i) := by
    dsimp [z]
    rw [Real.sqrt_mul (sub_nonneg.mpr ui)]
    nlinarith [sq_nonneg (Real.sqrt (1-u i) - Real.sqrt (1-v i)),
      Real.sq_sqrt (sub_nonneg.mpr ui), Real.sq_sqrt (sub_nonneg.mpr vi)]
  exact ⟨i, by linarith [hleft i, hright i, hmismatch i]⟩


/-- An independent pair of draws from `w` disagrees off the diagonal with
probability `1 - ∑ wᵢ²`. It is bounded by twice the exception probability
of any specified label. -/
theorem independent_label_mismatch {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (i : ι) : 1 - (∑ l, w l ^ 2) ≤ 2 * (1-w i) := by
  have h : w i ^ 2 ≤ ∑ l, w l ^ 2 :=
    Finset.single_le_sum (fun l _ => sq_nonneg (w l)) (Finset.mem_univ i)
  nlinarith [sq_nonneg (1 - w i)]

/-- The bound 28 in the second conclusion of the matching lemma, for
each marginal of the label law. Besides the two rectangle estimates, the
hypotheses are the one- and two-exception event inclusions from the edge law.
Independent disagreement is written as one minus the diagonal mass of the
product law. -/
theorem independent_mismatch_le_twenty_eight {ι : Type*} [Fintype ι] [Nonempty ι]
    (u v d p q j : ι → ℝ) {s ξ : ℝ}
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (hU : ∑ i, u i = 1) (hV : ∑ i, v i = 1)
    (hp : ∀ i, p i ≤ 1) (hq : ∀ i, q i ≤ 1)
    (hξ : 0 ≤ ξ) (hξsmall : ξ ≤ 1 / (2 : ℝ)^100) (hs : 0 ≤ s)
    (hdiag : 1 - s = ∑ i, d i)
    (hcut : ∀ i, d i ≤ Real.sqrt (u i * v i) *
      ((Real.sqrt (u i * v i)) ^ (2 / 25 : ℝ) + ξ))
    (hcomp : ∀ i, j i ≤ Real.sqrt ((1-u i)*(1-v i)) *
      ((Real.sqrt ((1-u i)*(1-v i))) ^ (2 / 25 : ℝ) + ξ))
    (hleft : ∀ i, (27/50 : ℝ)*(1-u i) ≤ 1-p i)
    (hright : ∀ i, (27/50 : ℝ)*(1-v i) ≤ 1-q i)
    (hmismatch : ∀ i, (1-p i) + (1-q i) - 2 * j i ≤ s)
    (hexceptions : ∀ i, 1-p i ≤ s+j i ∧ 1-q i ≤ s+j i) :
    1 - (∑ l, p l^2) ≤ 28*s ∧ 1 - (∑ l, q l^2) ≤ 28*s := by
  by_cases tiny : s ≤ 1 / (2 : ℝ)^52
  · obtain ⟨i, hi⟩ := small_mismatch_dominant_label u v d (fun i => 1-p i) (fun i => 1-q i)
      j hu hv hU hV hξ hξsmall tiny hdiag hcut hcomp hleft hright hmismatch
    exact ⟨by linarith [independent_label_mismatch p i, hq i],
      by linarith [independent_label_mismatch q i, hp i]⟩
  by_cases large : 1 / 28 ≤ s
  · constructor <;> linarith [Finset.sum_nonneg (s := Finset.univ) (fun i _ => sq_nonneg (p i)),
      Finset.sum_nonneg (s := Finset.univ) (fun i _ => sq_nonneg (q i))]
  have hsξ : s + ξ ≤ 1 := by norm_num1 at hξsmall; linarith
  obtain ⟨i, hbound⟩ := dominant_counting_label u v d hu hv hU hV hξ hsξ hdiag hcut
  let z := Real.sqrt ((1-u i)*(1-v i))
  have hzn : 0 ≤ z := Real.sqrt_nonneg _
  change z ≤ _ at hbound
  have hz1 : z ≤ 1 := by norm_num1 at hξsmall; linarith
  have hpow : z ^ (2/25 : ℝ) ≤ 1 := Real.rpow_le_one hzn hz1 (by norm_num)
  have hj := hcomp i
  change j i ≤ z * (z ^ (2/25 : ℝ) + ξ) at hj
  have factor : z * (z ^ (2/25 : ℝ) + ξ) ≤ z * (1 + 1/100 : ℝ) :=
    mul_le_mul_of_nonneg_left (by norm_num1 at hξsmall; linarith) hzn
  have ratio : ξ ≤ s/100 := by norm_num1 at hξsmall tiny; linarith
  exact ⟨by linarith [(hexceptions i).1, independent_label_mismatch p i],
    by linarith [(hexceptions i).2, independent_label_mismatch q i]⟩


/-- Mass of a cell in the two-by-two partition according as each observed
label equals `a`, under a genuine finite joint law. -/
noncomputable def labelEvent {Ω : Type*} [Fintype Ω] (m : Ω → ℝ) (F : Ω → Prop) : ℝ :=
  ∑ e, @ite ℝ (F e) (Classical.propDecidable _) (m e) 0

/-- Both conclusions of the manuscript's finite matching lemma, for actual
label maps on a finite edge probability space. The expansion and degree
premises are needed only for a single label and the two complementary sets.
They are the corresponding instances of the graph's rectangle and marginal
bounds, after pushing vertex counting measures to the finite label set. -/
theorem matching_for_edge_law {Ω ι : Type*} [Fintype Ω] [Fintype ι] [Nonempty ι]
    (mass : Ω → ℝ) (left right : Ω → ι) (u v : ι → ℝ) (ξ : ℝ)
    (hm : ∀ e, 0 ≤ mass e) (hΩ : ∑ e, mass e = 1)
    (hu : ∀ a, 0 ≤ u a) (hv : ∀ a, 0 ≤ v a)
    (hU : ∑ a, u a = 1) (hV : ∑ a, v a = 1)
    (hξ : 0 ≤ ξ) (hξsmall : ξ ≤ 1/(2 : ℝ)^100)
    (hcut : ∀ a, labelEvent mass (fun e => left e = a ∧ right e = a) ≤
      Real.sqrt (u a * v a) * ((Real.sqrt (u a * v a)) ^ (2/25 : ℝ) + ξ))
    (hcomp : ∀ a, labelEvent mass (fun e => left e ≠ a ∧ right e ≠ a) ≤
      Real.sqrt ((1-u a)*(1-v a)) * ((Real.sqrt ((1-u a)*(1-v a))) ^ (2/25 : ℝ) + ξ))
    (hleft : ∀ a, (27/50 : ℝ)*(1-u a) ≤ labelEvent mass (fun e => left e ≠ a))
    (hright : ∀ a, (27/50 : ℝ)*(1-v a) ≤ labelEvent mass (fun e => right e ≠ a)) :
    let s := labelEvent mass (fun e => left e ≠ right e)
    (s ≤ 1 / (2 : ℝ)^52 → ∃ a,
      labelEvent mass (fun e => left e ≠ a) + labelEvent mass (fun e => right e ≠ a) ≤ 2*s) ∧
    (1 - (∑ a, (labelEvent mass (fun e => left e = a))^2) ≤ 28*s ∧
     1 - (∑ a, (labelEvent mass (fun e => right e = a))^2) ≤ 28*s) := by
  classical
  let s := labelEvent mass (fun e => left e ≠ right e)
  let p (a : ι) := labelEvent mass (fun e => left e = a)
  let q (a : ι) := labelEvent mass (fun e => right e = a)
  let d (a : ι) := labelEvent mass (fun e => left e = a ∧ right e = a)
  let j (a : ι) := labelEvent mass (fun e => left e ≠ a ∧ right e ≠ a)
  let E := labelEvent mass
  have nonneg (F : Ω → Prop) : 0 ≤ E F := by
    unfold E labelEvent
    apply Finset.sum_nonneg
    intro e _
    split_ifs <;> simp [hm]
  have compl (F : Ω → Prop) : 1 - E F = E (fun e => ¬F e) := by
    rw [sub_eq_iff_eq_add, ← hΩ]
    simp only [E, labelEvent, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by by_cases he : F e <;> simp [he]
  have hdiag : 1 - s = ∑ a, d a := by
    rw [show s = E (fun e => left e ≠ right e) from rfl, compl]
    simp only [d, E, labelEvent, not_not]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    by_cases lr : left e = right e
    · simp [lr, eq_comm]
    · have impossible (a : ι) : ¬(left e = a ∧ right e = a) :=
        fun ha => lr (ha.1.trans ha.2.symm)
      simp [lr, impossible]
  have families (a : ι) :
      (1-p a) + (1-q a) - 2*j a ≤ s ∧
      1-p a ≤ s+j a ∧ 1-q a ≤ s+j a := by
    change (1-E (fun e => left e = a)) + (1-E (fun e => right e = a)) - 2*j a ≤ s ∧
      1-E (fun e => left e = a) ≤ s+j a ∧ 1-E (fun e => right e = a) ≤ s+j a
    rw [compl, compl]
    simp only [j, s, E, labelEvent, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    constructor
    · apply Finset.sum_le_sum
      intro e _
      by_cases h₁ : left e = a <;> by_cases h₂ : right e = a <;>
        by_cases h₃ : left e = right e <;> simp_all <;> linarith [hm e]
    · constructor <;> apply Finset.sum_le_sum <;> intro e _ <;>
        by_cases h₁ : left e = a <;> by_cases h₂ : right e = a <;>
        by_cases h₃ : left e = right e <;> simp_all
  have loL (a : ι) : 27/50*(1-u a) ≤ 1-p a := (compl (fun e => left e = a)).symm ▸ hleft a
  have loR (a : ι) : 27/50*(1-v a) ≤ 1-q a := (compl (fun e => right e = a)).symm ▸ hright a
  have np (a : ι) : p a ≤ 1 := by linarith [compl (fun e => left e = a), nonneg (fun e => left e ≠ a)]
  have nq (a : ι) : q a ≤ 1 := by linarith [compl (fun e => right e = a), nonneg (fun e => right e ≠ a)]
  have hs : 0 ≤ s := nonneg _
  constructor
  · intro ht
    obtain ⟨a, ha⟩ := small_mismatch_dominant_label u v d (fun a => 1-p a) (fun a => 1-q a)
      j hu hv hU hV hξ hξsmall ht hdiag hcut hcomp loL loR (fun a => (families a).1)
    refine ⟨a, ?_⟩
    change E (fun e => left e ≠ a) + E (fun e => right e ≠ a) ≤ 2*s
    rw [← compl (fun e => left e = a), ← compl (fun e => right e = a)]
    exact ha
  · exact independent_mismatch_le_twenty_eight u v d p q j hu hv hU hV np nq hξ hξsmall hs hdiag
      hcut hcomp loL loR (fun a => (families a).1) (fun a => (families a).2)

end PlanarUnitDistances

