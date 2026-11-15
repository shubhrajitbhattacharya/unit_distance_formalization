import PlanarUnitDistances.HistoryCoupling
import PlanarUnitDistances.BoundedHeight

namespace PlanarUnitDistances.BoundedHeight
open OAI.PlanarUnitDistances.FiniteInformation Finset
open scoped BigOperators Classical
noncomputable section

variable {Q P A : Type*} [Fintype Q] [Fintype P] [DecidableEq A]

private theorem swap {I J : Type*} [Fintype I] [Fintype J] (f : I → J → ℝ) :
    ∑ i, ∑ j, f i j = ∑ j, ∑ i, f i j := Finset.sum_comm

/-- The three variables are the center, original point, and independent
resampling from the original point's history class. -/
def joint (κ : Q → ℝ) (w : Q → P → ℝ) (h : P → A) (ω : Q × P × P) : ℝ :=
  κ ω.1 * w ω.1 ω.2.1 * posterior (marginal κ w) h (h ω.2.1) ω.2.2

theorem joint_center (κ : Q → ℝ) (w : Q → P → ℝ) (h : P → A)
    (hm : ∀ p, 0 < marginal κ w p) (hsw : ∀ q, ∑ p, w q p = 1) (f : Q → ℝ) :
    ∑ ω, joint κ w h ω * f ω.1 = ∑ q, κ q * f q := by
  have row (q : Q) (p : P) : (∑ r, joint κ w h (q,p,r) * f q) = (κ q * w q p) * f q := by
    simp only [joint, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [posterior_sum _ hm h p, mul_one]
  simp only [Fintype.sum_prod_type]
  simp_rw [row]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, hsw, mul_one]

theorem joint_predicted (κ : Q → ℝ) (w : Q → P → ℝ) (h : P → A)
    (hm : ∀ p, 0 < marginal κ w p) (f : P → ℝ) :
    ∑ ω, joint κ w h ω * f ω.2.2 = ∑ p, marginal κ w p * f p := by
  simp only [Fintype.sum_prod_type, joint]
  rw [Finset.sum_comm]
  simp_rw [swap (I := Q) (J := P)]
  simp only [← Finset.sum_mul]
  change (∑ p, ∑ r, marginal κ w p * posterior (marginal κ w) h (h p) r * f r) = _
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, posterior_stationary _ hm]

theorem joint_exact {K : Type*} [Field K] (κ : Q → ℝ) (w : Q → P → ℝ) (h : P → A)
    (hm : ∀ p, 0 < marginal κ w p) (hsμ : ∑ p, marginal κ w p = 1)
    (centers : P → Finset Q)
    (hrev : ∀ q p, κ q * w q p = marginal κ w p *
      (if q ∈ centers p then 1/((centers p).card : ℝ) else 0))
    (zp wp : P → K) (zq wq : Q → K)
    (hzp : Function.Injective zp) (hzq : Function.Injective zq)
    (hedge : ∀ p q, q ∈ centers p → (zp p-zq q)*(wp p-wq q) = 1)
    {θ d : ℝ} (hθ : 0 ≤ θ) (hatom : ∀ p, marginal κ w p ≤ θ)
    (hd : 0 < d) (hdeg : ∀ p, d ≤ (centers p).card) :
    (∑ ω, joint κ w h ω * (if (zp ω.2.2-zq ω.1)*(wp ω.2.2-wq ω.1) = 1 then 1 else 0)) ≤
      ((univ.image h).card : ℝ) * θ + 2/d := by
  classical
  let μ := marginal κ w
  let π p r := posterior μ h (h p) r
  let e r q := (zp r-zq q)*(wp r-wq q) = 1
  let hit p r := ((centers p).filter (fun q => e r q)).card / ((centers p).card : ℝ)
  have each (p r : P) : (∑ q, joint κ w h (q,p,r) * (if e r q then 1 else 0)) =
      μ p * π p r * hit p r := by
    have term (q : Q) : joint κ w h (q,p,r) * (if e r q then 1 else 0) =
        if q ∈ centers p ∧ e r q then μ p * π p r / (centers p).card else 0 := by
      unfold joint
      dsimp only
      rw [hrev]
      by_cases hq : q ∈ centers p <;> by_cases he : e r q <;> simp [hq,he,μ,π]
      ring
    simp only [term, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have sets : (univ.filter fun q => q ∈ centers p ∧ e r q) = (centers p).filter (e r) := by
      ext q
      simp
    rw [sets]
    dsimp [hit]
    ring
  show (∑ ω : Q×P×P, joint κ w h ω * (if e ω.2.2 ω.1 then 1 else 0)) ≤ _
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp_rw [swap (I := Q) (J := P)]
  simp only [each]
  have bd (p r : P) : μ p * π p r * hit p r ≤
      μ p * π p r * ((if p=r then 1 else 0) + 2/d) :=
    mul_le_mul_of_nonneg_left (single_center centers zp wp zq wq hzp hzq hedge p r d hd (hdeg p))
      (mul_nonneg (hm p).le (posterior_nonneg μ hm h p r))
  refine (sum_le_sum (fun p _ => sum_le_sum (fun r _ => bd p r))).trans ?_
  have row (p : P) : (∑ r, μ p * π p r * ((if p=r then 1 else 0) + 2/d)) =
      μ p * π p p + μ p*(2/d) := by
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.sum_mul, ← Finset.mul_sum,
      π]
    rw [posterior_sum μ hm h p, mul_one]
  have ss : ∑ p, μ p = 1 := hsμ
  simp only [row, Finset.sum_add_distrib, ← Finset.sum_mul, ss, one_mul]
  linarith only [posterior_collision μ hm h hθ hatom]

end
end PlanarUnitDistances.BoundedHeight
