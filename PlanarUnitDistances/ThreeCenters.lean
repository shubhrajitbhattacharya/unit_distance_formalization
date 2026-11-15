import PlanarUnitDistances.Geometry
import PlanarUnitDistances.Matching

/-! # The three-center obstruction

There is one predicted point per outcome, shared by all three tests. Test
randomness, including a shared embedding, can be included in the outcome.
-/

namespace PlanarUnitDistances
open Finset
open scoped BigOperators
noncomputable section

/-- When the independent history-class resampling is used, its diagonal mass
is the displayed sum. An occupied record contributes at most one point atom. -/
theorem history_resampling_collision {P H : Type*} [Fintype P] [DecidableEq H]
    (μ : P → ℝ) (hist : P → H) {θ : ℝ}
    (hμ : ∀ p, 0 ≤ μ p) (hθ : 0 ≤ θ) (hatom : ∀ p, μ p ≤ θ) :
    let records := Finset.univ.image hist
    let classMass := fun a => ∑ p ∈ Finset.univ.filter (fun p => hist p = a), μ p
    (∑ p, μ p * (μ p / classMass (hist p))) ≤ (records.card : ℝ) * θ := by
  classical
  intro records classMass
  have each (a : H) :
      (∑ p ∈ Finset.univ.filter (fun p => hist p = a), μ p * (μ p / classMass (hist p))) ≤ θ := by
    let F := Finset.univ.filter (fun p => hist p = a)
    have eqv (p : P) (hp : p ∈ F) : hist p = a := (Finset.mem_filter.mp hp).2
    have sumEq : (∑ p ∈ F, μ p * (μ p / classMass (hist p))) =
        (∑ p ∈ F, μ p * μ p) / classMass a := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun p hp => by rw [eqv p hp]; ring)
    change (∑ p ∈ F, μ p * (μ p / classMass (hist p))) ≤ θ
    rw [sumEq]
    by_cases hz : classMass a = 0
    · simpa [hz] using hθ
    have ha : 0 < classMass a := lt_of_le_of_ne (Finset.sum_nonneg fun p _ => hμ p) (Ne.symm hz)
    apply (div_le_iff₀ ha).2
    change (∑ p ∈ F, μ p * μ p) ≤ θ * ∑ p ∈ F, μ p
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_right (hatom p) (hμ p)
  have split := Finset.sum_fiberwise_of_maps_to (g := hist) (s := Finset.univ) (t := records)
    (fun p hp => Finset.mem_image_of_mem hist hp) (fun p => μ p * (μ p / classMass (hist p)))
  calc
    _ = _ := split.symm
    _ ≤ ∑ _a ∈ records, θ := Finset.sum_le_sum fun a _ => each a
    _ = _ := by simp [nsmul_eq_mul]


end
end PlanarUnitDistances

