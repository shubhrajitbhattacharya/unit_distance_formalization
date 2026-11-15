import PlanarUnitDistances.GeometricCodegree
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! The exceptional unit circles removed before assigning a center to each
ordered pair. The family of rich circles ranges over every center in the real
Euclidean plane, independently of the center set of the incidence graph. -/

noncomputable section
namespace PlanarUnitDistances

open OAI.PlanarUnitDistances Finset

/-- Points of the input on the circle with center c. -/
noncomputable def circlePoints (P : Finset Plane) (c : Plane) : Finset Plane := by
  classical exact P.filter (fun p ↦ dist p c = 1)

@[simp] theorem mem_circlePoints {P : Finset Plane} {p c : Plane} :
    p ∈ circlePoints P c ↔ p ∈ P ∧ dist p c = 1 := by
  classical exact mem_filter

/-- All centers of circles containing at least m input points. -/
def richCenterSet (P : Finset Plane) (m : ℕ) : Set Plane :=
  {c | m ≤ (circlePoints P c).card}

private theorem ordered_pair_count (P C : Finset Plane) (m : ℕ)
    (hr : ∀ c ∈ C, m ≤ (circlePoints P c).card) :
    C.card * (m*(m-1)) ≤ P.offDiag.card * 2 := by
  classical
  let rel := fun (c : Plane) (z : Plane × Plane) ↦ dist z.1 c = 1 ∧ dist z.2 c = 1
  have habove (c : Plane) : P.offDiag.bipartiteAbove rel c = (circlePoints P c).offDiag := by
    ext z
    simp only [mem_bipartiteAbove, mem_offDiag, mem_circlePoints, rel]
    tauto
  apply (Finset.card_nsmul_le_card_nsmul (R := ℕ) rel ?_ ?_)
  · intro c hc
    rw [habove, offDiag_card, ← Nat.mul_sub_one]
    exact Nat.mul_le_mul (hr c hc) (Nat.sub_le_sub_right (hr c hc) 1)
  · intro z hz
    apply planar_common_centers_le_two _ id Function.injective_id.injOn (mem_offDiag.mp hz).2.2
    · intro c hc; exact ((mem_bipartiteBelow rel).mp hc).2.1
    · intro c hc; exact ((mem_bipartiteBelow rel).mp hc).2.2

/-- Richness at least two makes the set of all geometric centers finite.
The result also gives its exact ordered-pair incidence bound. -/
theorem rich_circles_finite_count (P : Finset Plane) {m : ℕ} (hm : 2 ≤ m) :
    (richCenterSet P m).Finite ∧
      (richCenterSet P m).ncard * (m*(m-1)) ≤ P.offDiag.card * 2 := by
  classical
  have hf : (richCenterSet P m).Finite := by
    by_contra hinf
    obtain ⟨C, hC, hc⟩ := Set.Infinite.exists_subset_card_eq hinf (P.offDiag.card*2+1)
    have h := ordered_pair_count P C m (fun c hc ↦ hC hc)
    have hpos : 1 ≤ m*(m-1) := Nat.one_le_iff_ne_zero.mpr <| Nat.mul_ne_zero (by omega) (by omega)
    have hle := Nat.mul_le_mul_left C.card hpos
    rw [Nat.mul_one] at hle
    omega
  refine ⟨hf, ?_⟩
  have h := ordered_pair_count P hf.toFinset m (fun c hc ↦ hf.mem_toFinset.mp hc)
  rwa [← Set.ncard_eq_toFinset_card _ hf] at h

/-- Intersection multiplicity summed over the rich circles. The factor two
from two circle intersections cancels the two orderings of the center pair. -/
theorem double_covered_points_count (P C : Finset Plane) :
    (P.filter (fun p ↦ 2 ≤ (circlePoints C p).card)).card ≤ C.offDiag.card := by
  classical
  let bad := P.filter (fun p ↦ 2 ≤ (circlePoints C p).card)
  have h := ordered_pair_count C bad 2 (fun p hp ↦ (mem_filter.mp hp).2)
  change bad.card ≤ C.offDiag.card
  omega

/-- Converting the discrete count to the rectangular graph parameters in
the density theorem. The use of the ceiling covers noninteger thresholds. -/
theorem rich_circles_power_bound (P : Finset Plane) {t a : ℝ} (ht : 0 < t)
    (htwo : 2 ≤ t^(9/10 : ℝ)) (hP : (P.card : ℝ) ≤ 2*t^(1+2*a)) :
    ((richCenterSet P ⌈t^(9/10 : ℝ)⌉₊).ncard : ℝ) ≤ 16*t^(1/5+4*a) := by
  let m := ⌈t^(9/10 : ℝ)⌉₊
  have hm' : t^(9/10 : ℝ) ≤ (m:ℝ) := Nat.le_ceil _
  have hm : 2 ≤ m := by exact_mod_cast htwo.trans hm'
  have h := (rich_circles_finite_count P hm).2
  have hmn : ((m-1 : ℕ) : ℝ) = (m:ℝ)-1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hR : ((richCenterSet P m).ncard : ℝ) * ((m:ℝ)*((m:ℝ)-1)) ≤ (P.card:ℝ)^2 * 2 := by
    have h' : (richCenterSet P m).ncard * (m*(m-1)) ≤ P.card^2*2 :=
      h.trans (Nat.mul_le_mul_right _ (by rw [offDiag_card,pow_two]; omega))
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hmn] using
      (Nat.cast_le (α := ℝ)).mpr h'
  have hlow : (t^(9/10 : ℝ))^2/2 ≤ (m:ℝ)*((m:ℝ)-1) := by
    have hhalf : t^(9/10 : ℝ)/2 ≤ (m:ℝ)-1 := by linarith
    have hh := mul_le_mul hm' hhalf (by positivity) (Nat.cast_nonneg (α := ℝ) m)
    nlinarith only [hh]
  have hbound : ((richCenterSet P m).ncard : ℝ) * (t^(9/10 : ℝ))^2 ≤ 16*(t^(1+2*a))^2 := by
    have h₁ := mul_le_mul_of_nonneg_left hlow
      (Nat.cast_nonneg (α := ℝ) (richCenterSet P m).ncard)
    have h₂ := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) P.card) hP 2
    nlinarith only [h₁,hR,h₂]
  change ((richCenterSet P m).ncard : ℝ) ≤ 16*t^(1/5+4*a)
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < (t^(9/10 : ℝ))^2)).mp
  calc
    _ ≤ _ := hbound
    _ = 16*t^(1/5+4*a)*(t^(9/10 : ℝ))^2 := by
      simp only [sq, ← Real.rpow_add ht, mul_assoc]
      congr 2
      ring

/-- For a fixed first endpoint outside the double-covered set and a fixed
non-rich center, at most two of that center's neighbors can complete a
pair on a rich circle. This counts the geometric endpoints before any
choice of a witness center. -/
theorem forbidden_returns_le_two (C N : Finset Plane) {p q : Plane}
    (hq : q ∉ C) (hp : (circlePoints C p).card ≤ 1)
    (hN : ∀ r ∈ N, dist r q = 1) :
    (N.filter fun r ↦ ∃ c ∈ C, dist p c = 1 ∧ dist r c = 1).card ≤ 2 := by
  classical
  let F := N.filter fun r ↦ ∃ c ∈ C, dist p c = 1 ∧ dist r c = 1
  change F.card ≤ 2
  by_cases hf : F.Nonempty
  · obtain ⟨x,hx⟩ := hf
    obtain ⟨c,hc,hpc,_⟩ := (mem_filter.mp hx).2
    have hc₀ : c ∈ circlePoints C p := mem_circlePoints.mpr ⟨hc, by rwa [dist_comm]⟩
    apply planar_common_centers_le_two F id Function.injective_id.injOn
      (show c ≠ q by rintro rfl; exact hq hc)
    · intro r hr
      obtain ⟨c',hc',hpc',hrc'⟩ := (mem_filter.mp hr).2
      have hc'₀ : c' ∈ circlePoints C p := mem_circlePoints.mpr ⟨hc', by rwa [dist_comm]⟩
      have heq := card_le_one.mp hp c hc₀ c' hc'₀
      rw [heq,dist_comm]
      exact hrc'
    · intro r hr; exact (dist_comm q r).trans (hN r (mem_filter.mp hr).1)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hf]

/-- Probability lost from the actual uniform-incidence two-edge walk when an
ordered pair lies on a circle in C. The first endpoint alone is sufficient
for the first exceptional event. Edges and neighborhoods remain oriented
exactly as in the graph extraction. -/
theorem rich_circle_deletion_cost (P Q C : Finset Plane) (N : Plane → Finset Plane)
    {e d A B : ℝ} (he : 0 < e) (hd : 0 < d)
    (hmin : ∀ q ∈ Q, d ≤ ((N q).card : ℝ))
    (hsum : ∑ q ∈ Q, ((N q).card : ℝ) = e)
    (hsub : ∀ q ∈ Q, N q ⊆ P) (hunit : ∀ q ∈ Q, ∀ r ∈ N q, dist r q = 1)
    (hatom : ∀ p ∈ P, ((Q.filter fun q ↦ p ∈ N q).card : ℝ) / e ≤ A)
    (hcenter : ∀ q ∈ Q, ((N q).card : ℝ) / e ≤ B) :
    (∑ q ∈ Q, ∑ p ∈ N q, ∑ _r ∈ (N q).filter (fun r ↦
      ∃ c ∈ C, dist p c = 1 ∧ dist r c = 1),
        (e * ((N q).card : ℝ))⁻¹) ≤
      ((P.filter fun p ↦ 2 ≤ (circlePoints C p).card).card : ℝ)*A +
      (C.card:ℝ)*B + 2/d := by
  classical
  let bad := P.filter fun p ↦ 2 ≤ (circlePoints C p).card
  let n (q : Plane) : ℝ := (N q).card
  let forbidden (q p : Plane) := (N q).filter fun r ↦
    ∃ c ∈ C, dist p c = 1 ∧ dist r c = 1
  let m (q p : Plane) : ℝ := ∑ _r ∈ forbidden q p, (e*n q)⁻¹
  have hn (q : Plane) (hq : q ∈ Q) : 0 < n q := hd.trans_le (hmin q hq)
  have full (q p : Plane) (hq : q ∈ Q) : m q p ≤ e⁻¹ := by
    calc
      m q p = ((forbidden q p).card:ℝ)*(e*n q)⁻¹ := by simp [m]
      _ ≤ n q*(e*n q)⁻¹ := by
        gcongr
        exact (Nat.cast_le (α := ℝ)).mpr (Finset.card_filter_le (N q) _)
      _ = _ := by field_simp [ne_of_gt (hn q hq)]
  have localBound (q : Plane) (hq : q ∈ Q) (p : Plane) (hp : p ∈ N q) :
      m q p ≤ (if p ∈ bad then e⁻¹ else 0) + (if q ∈ C then e⁻¹ else 0) + 2/(e*d) := by
    have hn' := hn q hq
    have hinv : 0 ≤ e⁻¹ := (inv_pos.mpr he).le
    have hnon : 0 ≤ 2 / (e*d) := by positivity
    by_cases hb : p ∈ bad <;> by_cases hc : q ∈ C
    · simp [hb,hc]; linarith [full q p hq]
    · simp [hb,hc]; linarith [full q p hq]
    · simp [hb,hc]; linarith [full q p hq]
    · simp only [hb,hc,if_false,zero_add]
      have hp' : (circlePoints C p).card ≤ 1 := by
        by_contra! hh
        exact hb (mem_filter.mpr ⟨hsub q hq hp, by omega⟩)
      have hcut := forbidden_returns_le_two C (N q) hc hp' (hunit q hq)
      have hinv' := inv_anti₀ (mul_pos he hd) (mul_le_mul_of_nonneg_left (hmin q hq) he.le)
      calc
        _ = ((forbidden q p).card:ℝ)*(e*n q)⁻¹ := by simp [m]
        _ ≤ 2*(e*d)⁻¹ := mul_le_mul (by exact_mod_cast hcut) hinv' (by positivity) (by norm_num)
        _ = _ := by ring
  have hfirst : (∑ q ∈ Q, ∑ p ∈ N q, if p ∈ bad then e⁻¹ else 0) ≤ (bad.card:ℝ)*A := by
    calc
      _ = ∑ q ∈ Q, ∑ p ∈ bad, if p ∈ N q then e⁻¹ else 0 := by
        apply sum_congr rfl; intro q _
        rw [← sum_filter, ← sum_filter, filter_mem_eq_inter, filter_mem_eq_inter, inter_comm]
      _ = ∑ p ∈ bad, ((Q.filter fun q ↦ p ∈ N q).card:ℝ) / e := by
        rw [sum_comm]; apply sum_congr rfl; intro p _
        rw [← sum_filter]; simp [div_eq_mul_inv]
      _ ≤ _ := by
        simpa using sum_le_sum (s := bad) (fun p hp ↦ hatom p (mem_filter.mp hp).1)
  have hB : 0 ≤ B := by
    have hQ : Q.Nonempty := by
      by_contra! h; simp [h] at hsum; linarith
    obtain ⟨q,hq⟩ := hQ
    exact (div_nonneg (hn q hq).le he.le).trans (hcenter q hq)
  have hsecond : (∑ q ∈ Q, ∑ _p ∈ N q, if q ∈ C then e⁻¹ else 0) ≤ (C.card:ℝ)*B := by
    calc
      _ = ∑ q ∈ Q.filter (· ∈ C), ((N q).card : ℝ)/e := by
        rw [sum_filter]; apply sum_congr rfl; intro q _; by_cases hq : q ∈ C <;> simp [hq,div_eq_mul_inv]
      _ ≤ ((Q.filter (· ∈ C)).card:ℝ)*B := by
        simpa using sum_le_sum (s := Q.filter (· ∈ C)) (fun q hq ↦ hcenter q (mem_filter.mp hq).1)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hB
        exact_mod_cast card_le_card (show Q.filter (· ∈ C) ⊆ C from fun q hq ↦ (mem_filter.mp hq).2)
  have hthird : (∑ q ∈ Q, ∑ _p ∈ N q, 2/(e*d)) = 2/d := by
    simp only [sum_const,nsmul_eq_mul,← sum_mul,hsum]
    field_simp
  change (∑ q ∈ Q, ∑ p ∈ N q, m q p) ≤ _
  have hh := sum_le_sum (s := Q) (fun q hq ↦ sum_le_sum (s := N q) (fun p hp ↦ localBound q hq p hp))
  simp only [sum_add_distrib, hthird] at hh
  linarith

end PlanarUnitDistances
