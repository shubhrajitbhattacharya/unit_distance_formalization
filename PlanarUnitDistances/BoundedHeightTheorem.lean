import PlanarUnitDistances.UniformGraphHeight
import PlanarUnitDistances.Constants

namespace PlanarUnitDistances.BoundedHeight
open OAI.PlanarUnitDistances.FiniteInformation Finset Real
open scoped BigOperators Classical
noncomputable section


/-- The small-height contradiction at the exact exponent. The atom estimate
is written as t·θ≤0.01, so callers can supply any decay beyond t⁻¹. -/
theorem small_height_endpoint {P Q F : Type*} [Fintype P] [Fintype Q] [Field F] [NumberField F]
    (S : Q → Finset P) (hrow : ∀ q, (S q).Nonempty) {e : ℝ} (he : 0 < e)
    (heq : ∑ q, ((S q).card : ℝ) = e)
    (zp wp : P → F) (zq wq : Q → F) (hzp : Function.Injective zp) (hzq : Function.Injective zq)
    (hedge : ∀ q p, p ∈ S q → (zp p-zq q)*(wp p-wq q)=1)
    {θ t : ℝ} (hθ : 0 ≤ θ) (ht : 0 < t) (htθ : t*θ ≤ 1/100)
    (hatom : ∀ p, ((pointCenters S p).card : ℝ)/e ≤ θ)
    (hdeg : ∀ p, (300:ℝ) ≤ (pointCenters S p).card)
    (hD : twoEdgeInformation S e + 1 ≤ 30600*exactGap*log t) :
    H0 < (∑ p, ((pointCenters S p).card : ℝ)/e * (weilHeight (zp p)+weilHeight (wp p))) +
      (∑ q, centerLaw S e q * (weilHeight (zq q)+weilHeight (wq q))) := by
  let D := twoEdgeInformation S e
  let N := gridSize H0
  let M := N^4+1
  let L := sampleSize N D
  have hH : (1000:ℝ) ≤ H0 := by
    have h : (2:ℝ)^3 ≤ 2^2100 := pow_le_pow_right₀ (by norm_num) (by decide)
    norm_num only [show (2:ℝ)^3=8 by norm_num] at h
    unfold H0
    exact (show ∀ x : ℝ, 8 ≤ x → 1000 ≤ 226*(x+1) by intros; linarith) _ h
  have dpos : 0 ≤ D := twoEdgeInformation_nonneg S hrow he heq
  have nn := grid_positive H0
  have ll : 0 < L := sample_positive N nn D dpos
  have hlog := smallHeight_history_log_lt dpos hD
  change ((L:ℝ)-1)*log (1+(N:ℝ)^4) < log t at hlog
  have mp : 0 < (M:ℝ) := by dsimp [M]; positivity
  have size : ((M^(L-1) : ℕ) : ℝ) ≤ t := by
    apply (log_le_log_iff (by positivity) ht).mp
    rw [Nat.cast_pow, log_pow, Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one]
    simpa only [M, Nat.cast_add, Nat.cast_one, Nat.cast_pow, add_comm ((N:ℝ)^4)] using hlog.le
  have col := (mul_le_mul_of_nonneg_right size hθ).trans htθ
  by_contra! low
  exact budget_impossible hH dpos col
    (uniform_graph_budget S hrow he heq zp wp zq wq hzp hzq hedge hθ hatom
      (by norm_num : (0:ℝ) < 300) hdeg (by linarith : 0 < 6*H0) (by linarith : 0 < 7*H0)
      N L nn ll (grid_mesh H0) low)

end
end PlanarUnitDistances.BoundedHeight
