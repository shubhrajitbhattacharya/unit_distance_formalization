import PlanarUnitDistances.CrossScores

namespace OAI.PlanarUnitDistances.FiniteLaw
open Finset StarScore
open scoped Classical
noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Exactly the atoms with strictly positive probability. -/
abbrev PositiveAtom (μ : Law X) := {x : X // 0 < μ.val x}

private theorem positive_sum (μ : Law X) (f : X → ℝ) (hz : ∀ x, μ.val x = 0 → f x = 0) :
    (∑ x : PositiveAtom μ, f x.val) = ∑ x, f x := by
  classical
  let s := univ.filter (fun x => 0 < μ.val x)
  have mem (x : X) : x ∈ s ↔ 0 < μ.val x := by simp [s]
  rw [← Finset.sum_subtype s mem f]
  apply Finset.sum_subset (Finset.subset_univ s)
  intro x _ hx
  exact hz x (le_antisymm (le_of_not_gt (fun h => hx ((mem x).mpr h))) (μ.nonneg x))

/-- Removing zero atoms leaves the original masses normalized. -/
def onPositive (μ : Law X) : Law (PositiveAtom μ) where
  val x := μ.val x.val
  nonneg x := μ.nonneg x.val
  total := (positive_sum μ μ.val (fun _ h => h)).trans μ.total

theorem onPositive_avg (μ : Law X) (f : X → ℝ) :
    avg (onPositive μ) (fun x => f x.val) = avg μ f :=
  positive_sum μ (fun x => μ.val x * f x) (fun _ h => by rw [h,zero_mul])

theorem onPositive_event (μ : Law X) (p : X → Prop) :
    event (onPositive μ) (fun x => p x.val) = event μ p := by
  unfold event
  exact onPositive_avg μ (fun x => if p x then 1 else 0)

/-- Independent draws retain exactly their original joint law, including the diagonal. -/
theorem onPositive_pair_avg (μ : Law X) (ν : Law Y) (f : X × Y → ℝ) :
    avg (pair (onPositive μ) (onPositive ν)) (fun xy => f (xy.1.val,xy.2.val)) =
      avg (pair μ ν) f := by
  rw [pair_avg,pair_avg]
  calc
    _ = avg (onPositive μ) (fun x => avg ν (fun y => f (x.val,y))) :=
      avg_congr _ (fun x => onPositive_avg ν (fun y => f (x.val,y)))
    _ = _ := onPositive_avg μ (fun x => avg ν (fun y => f (x,y)))

theorem onPositive_frequency (μ : Law X) (bit : X → Bool) :
    frequency (onPositive μ) (fun x => bit x.val) = frequency μ bit :=
  onPositive_event μ (fun x => bit x = true)

theorem onPositive_variation (μ : Law X) (bit : X → Bool) :
    variation (onPositive μ) (fun x => bit x.val) = variation μ bit := by
  simp only [variation,onPositive_frequency]

end
end OAI.PlanarUnitDistances.FiniteLaw
