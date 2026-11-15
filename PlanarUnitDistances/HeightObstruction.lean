import PlanarUnitDistances.CoupledCenters
import PlanarUnitDistances.CirclePrediction

namespace PlanarUnitDistances.BoundedHeight
open OAI.PlanarUnitDistances.FiniteInformation Finset Real CircleCells
open scoped Classical BigOperators
noncomputable section

private theorem average_joint {T Q P A : Type*} [Fintype T] [Fintype Q] [Fintype P] [DecidableEq A]
    (κ : Q → ℝ) (w : Q → P → ℝ) (h : P → A) (test : T → Q → P → Prop) (m : ℝ) :
    (∑ t, ∑ q, κ q * ∑ p, w q p * ∑ r, posterior (marginal κ w) h (h p) r *
      (if test t q r then 1 else 0)) / m =
    ∑ ω, joint κ w h ω * (((univ.filter fun t => test t ω.1 ω.2.2).card : ℝ) / m) := by
  have term (t : T) : (∑ q, κ q * ∑ p, w q p * ∑ r, posterior (marginal κ w) h (h p) r *
      (if test t q r then 1 else 0)) =
      ∑ ω : Q×P×P, joint κ w h ω * (if test t ω.1 ω.2.2 then 1 else 0) := by
    simp only [Fintype.sum_prod_type, joint, Finset.mul_sum, mul_assoc]
  simp only [term]
  rw [Finset.sum_comm, Finset.sum_div]
  apply sum_congr rfl
  intro ω _
  rw [← Finset.mul_sum]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  ring

/-- Nonasymptotic bounded-height obstruction with fully explicit grid and
predictor parameters. The reverse edge law says that, given the original
point, the center is a uniform member of its actual neighborhood. -/
theorem bounded_height_budget {P Q F : Type*} [Fintype P] [Fintype Q] [Field F] [NumberField F]
    (κ : Q → ℝ) (w : Q → P → ℝ) (hk : ∀ q, 0 ≤ κ q) (hw : ∀ q p, 0 ≤ w q p)
    (hsκ : ∑ q, κ q = 1) (hsw : ∀ q, ∑ p, w q p = 1) (hm : ∀ p, 0 < marginal κ w p)
    (C : P → Finset Q) (S : Q → Finset P) (hz : ∀ p q, q ∈ C p ↔ p ∈ S q)
    (hsup : ∀ q p, w q p ≠ 0 → p ∈ S q)
    (hrev : ∀ q p, κ q * w q p = marginal κ w p *
      (if q ∈ C p then 1/((C p).card : ℝ) else 0))
    (zp wp : P → F) (zq wq : Q → F) (hzp : Function.Injective zp) (hzq : Function.Injective zq)
    (hedge : ∀ q p, p ∈ S q → (zp p-zq q)*(wp p-wq q) = 1)
    {θ d H a s : ℝ} (hθ : 0 ≤ θ) (hatom : ∀ p, marginal κ w p ≤ θ)
    (hd : 0 < d) (hdeg : ∀ p, d ≤ (C p).card) (ha : 0 < a) (hs : 0 < s)
    (N L : ℕ) (hN : 0 < N) (hL : 0 < L) (hmesh : 8*exp a*width (exp a) N ≤ exp (-s))
    (hmean : (∑ p, marginal κ w p * (weilHeight (zp p)+weilHeight (wp p))) +
      (∑ q, κ q * (weilHeight (zq q)+weilHeight (wq q))) ≤ H) :
    1 ≤ (((N^4+1)^(L-1) : ℕ) : ℝ)*θ + 2/d + H/a + (H+3*log 2)/s +
      36*N*(KL (wedge κ w) (fun pr : P×P => marginal κ w pr.1*marginal κ w pr.2)/(L:ℝ))^(1/4:ℝ) := by
  classical
  obtain ⟨n,hn,h,hsize,hpred⟩ := exists_circle_history κ w hk hw hsκ hsw zp wp zq wq S hsup hedge
    (a := a) hN hL
  let m := joint κ w h
  let Z (ω : Q×P×P) := zp ω.2.2
  let W (ω : Q×P×P) := wp ω.2.2
  let X (ω : Q×P×P) := zq ω.1
  let Y (ω : Q×P×P) := wq ω.1
  let test (φ : F →+* ℂ) (q : Q) (r : P) := passes (S q) zp wp (zp r) (wp r) (zq q) (wq q) (exp a) N hN φ
  let frac (ω : Q×P×P) := (((univ.filter fun t => test t ω.1 ω.2.2).card : ℝ) / Module.finrank ℚ F)
  have hnon (ω : Q×P×P) : 0 ≤ m ω :=
    mul_nonneg (mul_nonneg (hk _) (hw _ _)) (posterior_nonneg _ hm h _ _)
  have mass : ∑ ω, m ω = 1 := by
    simpa [m, hsκ] using joint_center κ w h hm hsw (fun _ => 1)
  have heights : (∑ ω, m ω * (weilHeight (Z ω)+weilHeight (W ω)+weilHeight (X ω)+weilHeight (Y ω))) ≤ H := by
    let fp (r : P) := weilHeight (zp r)+weilHeight (wp r)
    let fq (q : Q) := weilHeight (zq q)+weilHeight (wq q)
    have term (ω : Q×P×P) : m ω * (weilHeight (Z ω)+weilHeight (W ω)+weilHeight (X ω)+weilHeight (Y ω)) =
        joint κ w h ω * fp ω.2.2 + joint κ w h ω * fq ω.1 := by
      dsimp [m,fp,fq,Z,W,X,Y]
      ring
    simp only [term, Finset.sum_add_distrib]
    rw [joint_predicted κ w h hm fp, joint_center κ w h hm hsw fq]
    exact hmean
  have falseBd := false_acceptance_coupling m (fun ω => S ω.1) zp wp Z W X Y hnon mass
    (fun ω => hedge ω.1) ha hs hN hmesh heights
  have trueBd := joint_exact κ w h hm (marginal_sum κ w hsκ hsw) C hrev zp wp zq wq hzp hzq
    (fun p q hq => hedge q p ((hz p q).mp hq)) hθ hatom hd hdeg
  let edge (ω : Q×P×P) := (Z ω-X ω)*(W ω-Y ω)=1
  change (∑ ω, m ω * (if edge ω then 0 else frac ω)) ≤ _ at falseBd
  change (∑ ω, m ω * (if edge ω then 1 else 0)) ≤ _ at trueBd
  have bound (ω : Q×P×P) : frac ω ≤ 1 := by
    dsimp [frac]
    rw [← NumberField.Embeddings.card F ℂ]
    apply (div_le_one (Nat.cast_pos.mpr Fintype.card_pos)).mpr
    exact_mod_cast Finset.card_filter_le _ _
  have total : (∑ ω, m ω * frac ω) ≤ (∑ ω, m ω*(if edge ω then 1 else 0)) +
      (∑ ω, m ω*(if edge ω then 0 else frac ω)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ω _
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (hnon ω)
    by_cases he : edge ω <;> simp [he, bound]
  rw [average_joint κ w h test] at hpred
  change 1 - (∑ ω, m ω * frac ω) ≤ _ at hpred
  have hstates := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hsize : ((univ.image h).card:ℝ) ≤ _) hθ
  linarith

end
end PlanarUnitDistances.BoundedHeight
