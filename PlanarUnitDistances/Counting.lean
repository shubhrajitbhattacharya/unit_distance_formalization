import PlanarUnitDistances.Specialization

namespace PlanarUnitDistances

open OAI.PlanarUnitDistances

/-- The exponent is a fixed input. Both the constant and the cut-off 2 are uniform in n. -/
def PowerSaving (δ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → (u n : ℝ) ≤ C * (n : ℝ) ^ (4 / 3 - δ)

/-- Every element is an ordered pair of actual points of the configuration. -/
noncomputable def orderedPairs (P : Finset Plane) : Finset (Plane × Plane) := by
  classical
  exact (P ×ˢ P).filter fun e => dist e.1 e.2 = 1

theorem orderedPairs_card (P : Finset Plane) :
    (orderedPairs P).card = 2 * unitPairCount P := by
  classical
  let U := P.sym2.filter IsUnitPair
  let f : Plane × Plane → Sym2 Plane := fun e => s(e.1,e.2)
  have hf : ∀ e ∈ orderedPairs P, f e ∈ U := by
    intro e he
    rcases Finset.mem_filter.mp he with ⟨hP, hu⟩
    exact Finset.mem_filter.mpr ⟨Finset.mk_mem_sym2_iff.mpr (Finset.mem_product.mp hP), hu⟩
  have fibers (a : Sym2 Plane) (ha : a ∈ U) : ((orderedPairs P).filter (f · = a)).card = 2 := by
    induction a using Sym2.ind with
    | _ p q =>
      obtain ⟨hm, hu⟩ := Finset.mem_filter.mp ha
      obtain ⟨hp, hq⟩ := Finset.mk_mem_sym2_iff.mp hm
      change dist p q = 1 at hu
      have hne : p ≠ q := by rintro rfl; simp at hu
      have hset : (orderedPairs P).filter (f · = s(p,q)) = {(p,q),(q,p)} := by
        ext e
        have hsym : f e = s(p,q) ↔ e = (p,q) ∨ e = (q,p) := Sym2.mk_eq_mk_iff (p := e) (q := (p,q))
        simp only [Finset.mem_filter, hsym, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · exact And.right
        · rintro (rfl | rfl) <;> simp [orderedPairs, hp, hq, hu, dist_comm q p]
      rw [hset, Finset.card_pair (fun h => hne (congrArg Prod.fst h) : (p,q) ≠ (q,p))]
  calc
    _ = ∑ a ∈ U, ((orderedPairs P).filter (f · = a)).card := Finset.card_eq_sum_card_fiberwise hf
    _ = ∑ _a ∈ U, 2 := Finset.sum_congr rfl fibers
    _ = 2 * unitPairCount P := by simp [U, unitPairCount, Nat.mul_comm]

theorem powerSaving_iff_uniform (δ : ℝ) : PowerSaving δ ↔
    ∃ C : ℝ, 0 < C ∧ ∀ P : Finset Plane, 2 ≤ P.card →
      (unitPairCount P : ℝ) ≤ C * (P.card : ℝ) ^ (4 / 3 - δ) := by
  constructor
  · rintro ⟨C, hC, h⟩
    exact ⟨C, hC, fun P hP => (Nat.cast_le.mpr (unitPairCount_le_u P)).trans (h _ hP)⟩
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, fun n hn => ?_⟩
    obtain ⟨P, hP, hu⟩ := exists_maximizer n
    simpa only [hu, hP] using h P (hP ▸ hn)

/-- It suffices to prove the same fixed-exponent inequality on real algebraic sets.
The constant is preserved when passing back to arbitrary real coordinates. -/
theorem powerSaving_iff_algebraic (δ : ℝ) : PowerSaving δ ↔
    ∃ C : ℝ, 0 < C ∧ ∀ P : Finset Plane, 2 ≤ P.card →
      (∀ p ∈ P, ∀ k, IsAlgebraic ℚ (p k)) →
      (unitPairCount P : ℝ) ≤ C * (P.card : ℝ) ^ (4 / 3 - δ) := by
  rw [powerSaving_iff_uniform]
  constructor
  · rintro ⟨C, hC, h⟩
    exact ⟨C, hC, fun P hn _ => h P hn⟩
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, fun P hn => ?_⟩
    obtain ⟨Q, hc, hcount, halg⟩ := algebraic_set_specialization P
    exact (Nat.cast_le.mpr hcount).trans (hc ▸ h Q (hc ▸ hn) halg)


end PlanarUnitDistances
