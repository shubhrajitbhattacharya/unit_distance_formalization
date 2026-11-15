import PlanarUnitDistances.GeometricCodegree

/-! Converting a surviving event in the Euclidean two-edge walk into
an ordered graph with one fixed center for every retained pair. -/

noncomputable section

namespace PlanarUnitDistances

open OAI.PlanarUnitDistances
open Finset

/-- The projected event is a set of ordered endpoint pairs; each supplied
fiber contains precisely the centers surviving the chosen test. -/
noncomputable def goodOrderedPairs {P Q : Type*} [Fintype P]
    (centers : P × P → Finset Q) : Finset (P × P) := by
  classical
  exact univ.filter fun z ↦ (centers z).Nonempty

/-- `e` is the number of incidences. Center probability is deg(q)/e;
the other two factors are the two independent neighbor probabilities. -/
noncomputable def goodTripleMass {P Q : Type*} [Fintype P] [DecidableEq P]
    (neighbors : Q → Finset P) (centers : P × P → Finset Q) (e : ℝ) : ℝ :=
  ∑ z ∈ goodOrderedPairs centers, ∑ q ∈ centers z,
    ((neighbors q).card : ℝ) / e *
      (if z.1 ∈ neighbors q then ((neighbors q).card : ℝ)⁻¹ else 0) *
      (if z.2 ∈ neighbors q then ((neighbors q).card : ℝ)⁻¹ else 0)

/-- Euclidean extraction with the manuscript constant 32000. The event
may depend on the center. Its surviving fibers need only consist of
incident distinct endpoints. -/
theorem good_ordered_pairs_and_witnesses {P Q : Type*} [Fintype P] [Fintype Q]
    [DecidableEq P] (point : P → Plane) (center : Q → Plane)
    (hp : Function.Injective point) (hc : Function.Injective center)
    (neighbors : Q → Finset P)
    (hunit : ∀ q i, i ∈ neighbors q → dist (point i) (center q) = 1)
    (centers : P × P → Finset Q)
    (hgood : ∀ z q, q ∈ centers z →
      z.1 ≠ z.2 ∧ z.1 ∈ neighbors q ∧ z.2 ∈ neighbors q)
    {d ε : ℝ} (hd : 0 < d) (hmin : ∀ q, d ≤ ((neighbors q).card : ℝ))
    (e : ℝ) (he : 0 < e) (_hsum : ∑ q, ((neighbors q).card : ℝ) = e)
    (hmass : ε/16000 ≤ goodTripleMass neighbors centers e) :
    ε * e * d / 32000 ≤ ((goodOrderedPairs centers).card : ℝ) ∧
      ∃ witness : (z : ↥(goodOrderedPairs centers)) → Q,
        ∀ z, witness z ∈ centers z.val := by
  classical
  have hmem (z : P × P) (hz : z ∈ goodOrderedPairs centers) : (centers z).Nonempty :=
    (mem_filter.mp hz).2
  have hN (q : Q) : 0 < ((neighbors q).card : ℝ) := hd.trans_le (hmin q)
  have hpair (z : P × P) (hz : z ∈ goodOrderedPairs centers) : (centers z).card ≤ 2 := by
    obtain ⟨q,hq⟩ := hmem z hz
    have h := euclidean_unit_graph_codegree point center hp hc neighbors hunit _ _ (hgood z q hq).1
    apply le_trans (card_le_card ?_) h
    intro q' hq'
    exact mem_filter.mpr ⟨mem_univ _, (hgood z q' hq').2⟩
  have hbound : goodTripleMass neighbors centers e ≤
      ((goodOrderedPairs centers).card : ℝ) * (2 / (e*d)) := by
    unfold goodTripleMass
    calc
      _ ≤ ∑ _z ∈ goodOrderedPairs centers, 2 / (e*d) := by
        apply sum_le_sum
        intro z hz
        calc
          _ ≤ ∑ _q ∈ centers z, (e*d)⁻¹ := by
            apply sum_le_sum
            intro q hq
            have hm := (hgood z q hq).2
            rw [if_pos hm.1, if_pos hm.2]
            calc
              _ = (e * ((neighbors q).card : ℝ))⁻¹ := by field_simp
              _ ≤ _ := inv_anti₀ (mul_pos he hd) (mul_le_mul_of_nonneg_left (hmin q) he.le)
          _ ≤ _ := by
            simp only [sum_const, nsmul_eq_mul, div_eq_mul_inv]
            gcongr
            exact_mod_cast hpair z hz
      _ = _ := by simp
  constructor
  · have hh := (hmass.trans hbound)
    rw [mul_div_assoc'] at hh
    have hh' := (le_div_iff₀ (mul_pos he hd)).mp hh
    linarith
  · exact ⟨fun z ↦ (hmem z.val z.property).choose,
      fun z ↦ (hmem z.val z.property).choose_spec⟩

end PlanarUnitDistances
