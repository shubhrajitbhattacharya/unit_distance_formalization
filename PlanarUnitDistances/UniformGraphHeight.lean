import PlanarUnitDistances.HeightObstruction
import PlanarUnitDistances.HeightParameters

namespace PlanarUnitDistances.BoundedHeight
open OAI.PlanarUnitDistances.FiniteInformation Finset Real
open scoped BigOperators Classical
noncomputable section

/-- A finite edge set via a neighborhood on the center side. Isolated centers
are allowed and given an arbitrary probability row, since their marginal is zero. -/
def centerLaw {P Q : Type*} (S : Q → Finset P) (e : ℝ) (q : Q) : ℝ := (S q).card/e

def neighborLaw {P Q : Type*} [Fintype P] (S : Q → Finset P) (q : Q) (p : P) : ℝ :=
  if (S q).Nonempty then (if p ∈ S q then ((S q).card : ℝ)⁻¹ else 0) else (Fintype.card P : ℝ)⁻¹

def pointCenters {P Q : Type*} [Fintype Q] (S : Q → Finset P) (p : P) : Finset Q :=
  univ.filter fun q => p ∈ S q

def twoEdgeInformation {P Q : Type*} [Fintype P] [Fintype Q] (S : Q → Finset P) (e : ℝ) : ℝ :=
  let κ := centerLaw S e
  let w := neighborLaw S
  KL (wedge κ w) (fun z : P×P => marginal κ w z.1 * marginal κ w z.2)

/-- On the support of the center marginal this is its actual neighborhood.
Adding every point to an isolated center's row would create spurious cell
constraints, so we use a formulation restricted to the incident centers. -/
theorem uniform_graph_budget {P Q F : Type*} [Fintype P] [Fintype Q] [Field F] [NumberField F]
    (S : Q → Finset P) (hrow : ∀ q, (S q).Nonempty) {e : ℝ} (he : 0 < e)
    (heq : ∑ q, ((S q).card : ℝ) = e)
    (zp wp : P → F) (zq wq : Q → F) (hzp : Function.Injective zp) (hzq : Function.Injective zq)
    (hedge : ∀ q p, p ∈ S q → (zp p-zq q)*(wp p-wq q)=1)
    {θ d H a s : ℝ} (hθ : 0 ≤ θ) (hatom : ∀ p, ((pointCenters S p).card : ℝ)/e ≤ θ)
    (hd : 0 < d) (hdeg : ∀ p, d ≤ (pointCenters S p).card) (ha : 0 < a) (hs : 0 < s)
    (N L : ℕ) (hN : 0 < N) (hL : 0 < L) (hmesh : 8*exp a*CircleCells.width (exp a) N ≤ exp (-s))
    (hmean : (∑ p, ((pointCenters S p).card : ℝ)/e * (weilHeight (zp p)+weilHeight (wp p))) +
      (∑ q, centerLaw S e q * (weilHeight (zq q)+weilHeight (wq q))) ≤ H) :
    1 ≤ (((N^4+1)^(L-1) : ℕ) : ℝ)*θ + 2/d + H/a + (H+3*log 2)/s +
      36*N*(twoEdgeInformation S e/(L:ℝ))^(1/4:ℝ) := by
  classical
  let κ := centerLaw S e
  let w := neighborLaw S
  have nk (q : Q) : (0:ℝ) < (S q).card := Nat.cast_pos.mpr (card_pos.mpr (hrow q))
  have hk (q : Q) : 0 ≤ κ q := (div_pos (nk q) he).le
  have hw (q : Q) (p : P) : 0 ≤ w q p := by
    dsimp [w,neighborLaw]; rw [if_pos (hrow q)]; split_ifs <;> positivity
  have hsk : ∑ q, κ q = 1 := by dsimp [κ,centerLaw]; rw [← Finset.sum_div, heq, div_self he.ne']
  have hsw (q : Q) : ∑ p, w q p = 1 := by
    simp [w,neighborLaw,hrow, (nk q).ne']
  have step (q : Q) (p : P) : κ q*w q p = if p ∈ S q then e⁻¹ else 0 := by
    by_cases hp : p ∈ S q <;> simp [κ,w,neighborLaw,centerLaw,hrow,hp,div_eq_mul_inv]
    field_simp [(nk q).ne']
  have marg (p : P) : marginal κ w p = ((pointCenters S p).card : ℝ)/e := by
    simp [marginal, step, pointCenters, ← Finset.sum_filter, div_eq_mul_inv]
  have pm (p : P) : 0 < marginal κ w p := by rw [marg]; exact div_pos (hd.trans_le (hdeg p)) he
  have supp (q : Q) (p : P) : w q p ≠ 0 → p ∈ S q := by
    intro h
    by_contra hp
    exact h (by simp [w,neighborLaw,hrow,hp])
  have rev (q : Q) (p : P) : κ q*w q p = marginal κ w p *
      (if q ∈ pointCenters S p then 1/((pointCenters S p).card:ℝ) else 0) := by
    rw [marg,step]
    have hv : q ∈ pointCenters S p ↔ p ∈ S q := by simp [pointCenters]
    have np := (hd.trans_le (hdeg p)).ne'
    by_cases hp : p ∈ S q <;> simp [hp,hv,div_eq_mul_inv]
    field_simp [np]
  exact bounded_height_budget κ w hk hw hsk hsw pm (pointCenters S) S (by simp [pointCenters]) supp rev
    zp wp zq wq hzp hzq hedge hθ (fun p => (marg p).le.trans (hatom p)) hd hdeg ha hs N L hN hL hmesh
    (by simpa only [marg] using hmean)

theorem twoEdgeInformation_nonneg {P Q : Type*} [Fintype P] [Fintype Q] (S : Q → Finset P)
    (hrow : ∀ q, (S q).Nonempty) {e : ℝ} (he : 0 < e) (heq : ∑ q, ((S q).card : ℝ) = e) :
    0 ≤ twoEdgeInformation S e := by
  let κ := centerLaw S e
  let w := neighborLaw S
  have hk (q : Q) : 0 ≤ κ q := div_nonneg (Nat.cast_nonneg _) he.le
  have hw (q : Q) (p : P) : 0 ≤ w q p := by
    dsimp [w,neighborLaw]; split_ifs <;> positivity
  have hsκ : ∑ q, κ q = 1 := by dsimp [κ,centerLaw]; rw [← Finset.sum_div, heq, div_self he.ne']
  have hsw (q : Q) : ∑ p, w q p = 1 := by
    have hp : (0:ℝ) < (S q).card := Nat.cast_pos.mpr (card_pos.mpr (hrow q))
    simp [w,neighborLaw,hrow, hp.ne']
  have hm := marginal_nonneg κ w hk hw
  have hs := marginal_sum κ w hsκ hsw
  apply KL_nonneg _ _ (wedge_nonneg κ w hk hw) (fun pr => mul_nonneg (hm _) (hm _))
    (wedge_sum κ w hsκ hsw) _ (wedge_ac κ w hk hw)
  rw [Fintype.sum_prod_type, ← sum_mul_sum, hs, one_mul]


end
end PlanarUnitDistances.BoundedHeight
