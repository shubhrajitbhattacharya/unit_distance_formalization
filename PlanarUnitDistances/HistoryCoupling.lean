import PlanarUnitDistances.Information
import PlanarUnitDistances.ThreeCenters

namespace PlanarUnitDistances.BoundedHeight
open OAI.PlanarUnitDistances.FiniteInformation Finset
open scoped BigOperators Classical
noncomputable section

variable {P A : Type*} [Fintype P] [DecidableEq A]

theorem class_mass_pos (μ : P → ℝ) (hμ : ∀ p, 0 < μ p) (h : P → A) (p : P) :
    0 < push μ h (h p) := by
  unfold push
  apply Finset.sum_pos' (fun r _ => by split_ifs <;> first | exact (hμ r).le | rfl)
  exact ⟨p, mem_univ _, by simp [hμ]⟩

theorem posterior_nonneg (μ : P → ℝ) (hμ : ∀ p, 0 < μ p) (h : P → A) (p r : P) :
    0 ≤ posterior μ h (h p) r := by
  unfold posterior
  exact div_nonneg (by split_ifs <;> first | exact (hμ r).le | rfl)
    (class_mass_pos μ hμ h p).le

theorem posterior_sum (μ : P → ℝ) (hμ : ∀ p, 0 < μ p) (h : P → A) (p : P) :
    ∑ r, posterior μ h (h p) r = 1 := by
  simp only [posterior, ← Finset.sum_div]
  exact div_self (class_mass_pos μ hμ h p).ne'

theorem posterior_stationary (μ : P → ℝ) (hμ : ∀ p, 0 < μ p) (h : P → A) (r : P) :
    ∑ p, μ p * posterior μ h (h p) r = μ r := by
  have term (p : P) : μ p * posterior μ h (h p) r =
      (if h p = h r then μ p else 0) * (μ r / push μ h (h r)) := by
    by_cases he : h p = h r
    · simp [posterior, he]
    · simp [posterior, he, Ne.symm he]
  simp only [term, ← Finset.sum_mul]
  change push μ h (h r) * (μ r / push μ h (h r)) = μ r
  field_simp [(class_mass_pos μ hμ h r).ne']

theorem posterior_collision (μ : P → ℝ) (hμ : ∀ p, 0 < μ p) (h : P → A)
    {θ : ℝ} (hθ : 0 ≤ θ) (hc : ∀ p, μ p ≤ θ) :
    ∑ p, μ p * posterior μ h (h p) p ≤ ((univ.image h).card : ℝ)*θ := by
  have b := history_resampling_collision μ h (fun p => (hμ p).le) hθ hc
  simpa [posterior, push, Finset.sum_filter] using b

end
end PlanarUnitDistances.BoundedHeight
