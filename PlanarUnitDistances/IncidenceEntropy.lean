import PlanarUnitDistances.Information

/-! The entropy estimate for the two-edge law in `cb:finite-piece`.
The initial theorem accepts the actual equal marginals and an off-diagonal
point-mass cap. The graph's codegrees and minimum degree provide this cap. -/

noncomputable section

namespace PlanarUnitDistances

open OAI.PlanarUnitDistances.FiniteInformation
open Finset

private theorem negative_entropy_ge_neg_log_card {P : Type*} [Fintype P] [Nonempty P]
    (μ : P → ℝ) (hμ : ∀ i, 0 ≤ μ i) (hs : ∑ i, μ i = 1) :
    -Real.log (Fintype.card P) ≤ ∑ i, μ i * Real.log (μ i) := by
  have hN : (0:ℝ) < Fintype.card P := by exact_mod_cast Fintype.card_pos
  let uniform : P → ℝ := fun _ ↦ (Fintype.card P : ℝ)⁻¹
  have hu (i : P) : 0 < uniform i := inv_pos.mpr hN
  have huSum : ∑ i, uniform i = 1 := by simp [uniform, hN.ne']
  have hk := KL_nonneg μ uniform hμ (fun i ↦ (hu i).le) hs huSum (fun i _ ↦ (hu i).ne')
  have hsplit (i : P) : μ i * Real.log (μ i / uniform i) =
      μ i * Real.log (μ i) + μ i * Real.log (Fintype.card P) := by
    by_cases hz : μ i = 0
    · simp [hz]
    · rw [Real.log_div hz (hu i).ne']
      simp [uniform, Real.log_inv, mul_add]
  simp only [KL, hsplit, sum_add_distrib, ← sum_mul, hs, one_mul] at hk
  linarith

/-- An explicit KL bound for any joint law with the two equal marginals of
the two-edge walk. If L=e d_min/2, the off-diagonal cap is exactly 1/L. -/
theorem mutual_information_of_offdiag_cap {P : Type*} [Fintype P] [Nonempty P]
    (p : P × P → ℝ) (μ : P → ℝ)
    (hp : ∀ z, 0 ≤ p z) (hμ : ∀ i, 0 < μ i) (hs : ∑ i, μ i = 1)
    (hr : ∀ i, ∑ j, p (i,j) = μ i) (hc : ∀ j, ∑ i, p (i,j) = μ j)
    {L : ℝ} (_hL : 0 < L) (hcap : ∀ i j, i ≠ j → p (i,j) ≤ L⁻¹) :
    KL p (fun z ↦ μ z.1 * μ z.2) ≤
      2 * Real.log (Fintype.card P) - (1 - ∑ i, p (i,i)) * Real.log L := by
  classical
  have hpsum : ∑ z, p z = 1 := by rw [Fintype.sum_prod_type]; simpa only [hr] using hs
  have hsplit (z : P × P) :
      p z * Real.log (p z / (μ z.1 * μ z.2)) =
        p z * Real.log (p z) - p z * Real.log (μ z.1) - p z * Real.log (μ z.2) := by
    by_cases hz : p z = 0
    · simp [hz]
    · rw [Real.log_div hz (mul_pos (hμ _) (hμ _)).ne', Real.log_mul (hμ _).ne' (hμ _).ne']
      ring
  have hrows : (∑ z : P × P, p z * Real.log (μ z.1)) = ∑ i, μ i * Real.log (μ i) := by
    rw [Fintype.sum_prod_type]
    simp only [← sum_mul, hr]
  have hcols : (∑ z : P × P, p z * Real.log (μ z.2)) = ∑ i, μ i * Real.log (μ i) := by
    rw [Fintype.sum_prod_type, sum_comm]
    simp only [← sum_mul, hc]
  have hpoint (z : P × P) : p z * Real.log (p z) ≤
      -(p z * Real.log L) + (if z.1 = z.2 then p z else 0) * Real.log L := by
    by_cases hz : p z = 0
    · simp [hz]
    have hpos : 0 < p z := lt_of_le_of_ne (hp _) (Ne.symm hz)
    by_cases hd : z.1 = z.2
    · rw [if_pos hd, neg_add_cancel]
      have hval : p z ≤ 1 := by
        rw [← hpsum]
        exact single_le_sum (fun z _ ↦ hp z) (mem_univ _)
      exact mul_nonpos_of_nonneg_of_nonpos hpos.le (Real.log_nonpos hpos.le hval)
    · have hlog := Real.log_le_log hpos (hcap z.1 z.2 hd)
      rw [Real.log_inv] at hlog
      simpa [hd] using (mul_le_mul_of_nonneg_left hlog hpos.le)
  have hsum := sum_le_sum (s := univ) (fun z _ ↦ hpoint z)
  have hdiag : (∑ z : P × P, if z.1 = z.2 then p z else 0) = ∑ i, p (i,i) := by
    simp [Fintype.sum_prod_type]
  simp only [sum_add_distrib, sum_neg_distrib, ← sum_mul, hpsum, one_mul, hdiag] at hsum
  simp only [KL, hsplit, sum_sub_distrib, hrows, hcols]
  linarith [negative_entropy_ge_neg_log_card μ (fun i ↦ (hμ i).le) hs]

/-- The same assertion on the precise law obtained by sampling a center and
then two independent neighbors from its transition row. -/
theorem wedge_mutual_information_bound {P Q : Type*} [Fintype P] [Nonempty P] [Fintype Q]
    (κ : Q → ℝ) (w : Q → P → ℝ) (hκ : ∀ q, 0 ≤ κ q) (hw : ∀ q i, 0 ≤ w q i)
    (hsκ : ∑ q, κ q = 1) (hsw : ∀ q, ∑ i, w q i = 1)
    (hμ : ∀ i, 0 < marginal κ w i) {L : ℝ} (hL : 0 < L)
    (hcap : ∀ i j, i ≠ j → wedge κ w (i,j) ≤ L⁻¹) :
    KL (wedge κ w) (fun z ↦ marginal κ w z.1 * marginal κ w z.2) ≤
      2 * Real.log (Fintype.card P) - (1 - ∑ i, wedge κ w (i,i)) * Real.log L := by
  have hr (i : P) : ∑ j, wedge κ w (i,j) = marginal κ w i := by
    unfold wedge marginal
    rw [sum_comm]
    simp only [← mul_sum, hsw, mul_one]
  have hc (j : P) : ∑ i, wedge κ w (i,j) = marginal κ w j := by
    calc
      _ = ∑ i, wedge κ w (j,i) := by
        apply sum_congr rfl
        intro i _
        unfold wedge
        apply sum_congr rfl
        intro q _
        ring
      _ = _ := hr j
  exact mutual_information_of_offdiag_cap _ _ (wedge_nonneg κ w hκ hw) hμ
    (marginal_sum κ w hsκ hsw) hr hc hL hcap

/-- The entropy estimate directly on a finite bipartite graph. The parameter
`d` is a positive lower bound for the center degrees. The joint law here
is exactly center sampling proportional to degree followed by independent
uniform sampling on the two copies of its neighborhood. -/
theorem graph_wedge_mutual_information_bound {P Q : Type*} [Fintype P] [Nonempty P]
    [Fintype Q] [DecidableEq P] (neighbors : Q → Finset P) {d : ℝ} (hd : 0 < d)
    (hmin : ∀ q, d ≤ ((neighbors q).card : ℝ))
    (hcodeg : ∀ i j, i ≠ j →
      ((Finset.univ.filter fun q ↦ i ∈ neighbors q ∧ j ∈ neighbors q).card) ≤ 2)
    {e : ℝ} (he : 0 < e) (hsum : ∑ q, ((neighbors q).card : ℝ) = e)
    (hpoint : ∀ i, ∃ q, i ∈ neighbors q) :
    let κ := fun q ↦ ((neighbors q).card : ℝ) / e
    let w := fun q i ↦ if i ∈ neighbors q then ((neighbors q).card : ℝ)⁻¹ else 0
    KL (wedge κ w) (fun z ↦ marginal κ w z.1 * marginal κ w z.2) ≤
      2 * Real.log (Fintype.card P) - (1 - (Fintype.card Q : ℝ)/e) * Real.log (e*d/2) := by
  classical
  let n (q : Q) : ℝ := (neighbors q).card
  let κ (q : Q) := n q / e
  let w (q : Q) (i : P) := if i ∈ neighbors q then (n q)⁻¹ else 0
  change KL (wedge κ w) _ ≤ _
  have hn (q : Q) : 0 < n q := hd.trans_le (hmin q)
  have hκ (q : Q) : 0 < κ q := div_pos (hn q) he
  have hw (q : Q) (i : P) : 0 ≤ w q i := by
    dsimp [w]; split_ifs
    · exact (inv_pos.mpr (hn q)).le
    · exact le_rfl
  have hsκ : ∑ q, κ q = 1 := by
    dsimp [κ,n]; rw [← sum_div, hsum, div_self he.ne']
  have hsw (q : Q) : ∑ i, w q i = 1 := by
    simp [w]
    exact mul_inv_cancel₀ (hn q).ne'
  have hμ (i : P) : 0 < marginal κ w i := by
    obtain ⟨q,hq⟩ := hpoint i
    have hpos : 0 < κ q * w q i := by
      rw [show w q i = (n q)⁻¹ by simp [w,hq]]
      exact mul_pos (hκ q) (inv_pos.mpr (hn q))
    exact hpos.trans_le (single_le_sum (fun q _ ↦ mul_nonneg (hκ q).le (hw q i)) (mem_univ q))
  have hstep (q : Q) (i j : P) :
      κ q * w q i * w q j =
        if i ∈ neighbors q ∧ j ∈ neighbors q then (e*n q)⁻¹ else 0 := by
    by_cases hi : i ∈ neighbors q <;> by_cases hj : j ∈ neighbors q <;>
      simp [κ,w,hi,hj,(hn q).ne',div_eq_mul_inv,mul_inv_rev,mul_comm]
  have hdiag : (∑ i, wedge κ w (i,i)) = (Fintype.card Q : ℝ)/e := by
    simp only [wedge, hstep, and_self, sum_comm (s := univ (α := P)) (t := univ (α := Q))]
    have hf (q : Q) : (∑ i : P, if i ∈ neighbors q then (e * n q)⁻¹ else 0) = e⁻¹ := by
      simp
      change n q * ((n q)⁻¹ * e⁻¹) = e⁻¹
      rw [← mul_assoc, mul_inv_cancel₀ (hn q).ne', one_mul]
    simp only [hf]
    simp [div_eq_mul_inv]
  have hcap (i j : P) (hij : i ≠ j) : wedge κ w (i,j) ≤ (e*d/2)⁻¹ := by
    let common := univ.filter fun q ↦ i ∈ neighbors q ∧ j ∈ neighbors q
    have hcount : (common.card : ℝ) ≤ 2 := by exact_mod_cast hcodeg i j hij
    have hfit (q : Q) : (e*n q)⁻¹ ≤ (e*d)⁻¹ := inv_anti₀ (mul_pos he hd)
      (mul_le_mul_of_nonneg_left (hmin q) he.le)
    calc
      wedge κ w (i,j) = ∑ q ∈ common, (e*n q)⁻¹ := by simp [wedge,hstep,common,sum_filter]
      _ ≤ ∑ _q ∈ common, (e*d)⁻¹ := sum_le_sum fun q _ ↦ hfit q
      _ ≤ 2 * (e*d)⁻¹ := by simp; gcongr
      _ = (e*d/2)⁻¹ := by field_simp
  have h := wedge_mutual_information_bound κ w (fun q ↦ (hκ q).le) hw hsκ hsw hμ
    (by positivity : 0 < e*d/2) hcap
  rwa [hdiag] at h

end PlanarUnitDistances
