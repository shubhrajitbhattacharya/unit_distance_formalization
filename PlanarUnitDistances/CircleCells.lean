import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! The finite reciprocal-curve test. The real
axis mesh consists of N equal intervals. At the right endpoint the last
interval is closed. The extra code is the single overflow symbol. -/

noncomputable section
namespace PlanarUnitDistances.CircleCells

open Finset

/-- A cell index on [0,N] in units of the mesh width. Clamping only affects
the right endpoint on that closed interval. -/
def axis (N : ℕ) (hN : 0 < N) (x : ℝ) : Fin N :=
  ⟨min ⌊x⌋₊ (N-1), lt_of_le_of_lt (min_le_right _ _) (by omega)⟩

theorem axis_interior {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : x < N) :
    (axis N hN x).val = ⌊x⌋₊ := by
  have : ⌊x⌋₊ < N := (Nat.floor_lt' hN.ne').mpr hx
  exact min_eq_left (by omega)

theorem axis_right {N : ℕ} (hN : 0 < N) : (axis N hN (N : ℝ)).val = N - 1 := by
  simp [axis]

private theorem axis_bounds {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : 0 ≤ x) (hu : x ≤ N) :
    ((axis N hN x).val : ℝ) ≤ x ∧ x ≤ (axis N hN x).val + 1 := by
  rcases hu.lt_or_eq with hu | rfl
  · rw [axis_interior hN hu]
    exact ⟨Nat.floor_le hx, (Nat.lt_floor_add_one _).le⟩
  · rw [axis_right, Nat.cast_sub (by omega : 1 ≤ N)]
    simp

def width (R : ℝ) (N : ℕ) : ℝ := 2 * R / N
def realCell (R : ℝ) (N : ℕ) (hN : 0 < N) (x : ℝ) : Fin N :=
  axis N hN ((x + R) / width R N)

private theorem realCell_bounds {R : ℝ} {N : ℕ} (hR : 0 < R) (hN : 0 < N)
    (x : ℝ) (hx : |x| ≤ R) :
    (realCell R N hN x).val * width R N ≤ x + R ∧
    x + R ≤ ((realCell R N hN x).val + 1) * width R N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < width R N := by dsimp [width]; positivity
  have htop : (N : ℝ) * width R N = 2 * R := by unfold width; field_simp
  obtain ⟨hl, hu⟩ := abs_le.mp hx
  have ht : (x + R) / width R N ≤ N := (div_le_iff₀ hw).mpr (by linarith)
  obtain ⟨h1,h2⟩ := axis_bounds hN (div_nonneg (by linarith) hw.le) ht
  exact ⟨(le_div_iff₀ hw).mp h1, (div_le_iff₀ hw).mp h2⟩

abbrev Cell (N : ℕ) := Fin N × Fin N
def cell (R : ℝ) (N : ℕ) (hN : 0 < N) (z : ℂ) : Cell N :=
  (realCell R N hN z.re, realCell R N hN z.im)

private theorem same_axis_near {R : ℝ} {N : ℕ} (hR : 0 < R) (hN : 0 < N)
    {x y : ℝ} (hx : |x| ≤ R) (hy : |y| ≤ R)
    (h : realCell R N hN x = realCell R N hN y) : |x-y| ≤ width R N := by
  have h1 := realCell_bounds hR hN x hx
  have h2 := realCell_bounds hR hN y hy
  rw [h] at h1
  apply abs_le.mpr
  constructor <;> nlinarith [h1.1,h1.2,h2.1,h2.2]

theorem same_cell_near {R : ℝ} {N : ℕ} (hR : 0 < R) (hN : 0 < N)
    {z w : ℂ} (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) (h : cell R N hN z = cell R N hN w) :
    ‖z-w‖ ≤ 2 * width R N := by
  have h1 := same_axis_near hR hN ((Complex.abs_re_le_norm z).trans hz)
    ((Complex.abs_re_le_norm w).trans hw) (congrArg Prod.fst h)
  have h2 := same_axis_near hR hN ((Complex.abs_im_le_norm z).trans hz)
    ((Complex.abs_im_le_norm w).trans hw) (congrArg Prod.snd h)
  have ht := Complex.norm_le_abs_re_add_abs_im (z-w)
  simp only [Complex.sub_re, Complex.sub_im] at ht
  linarith

private theorem axis_index_gap {R : ℝ} {N : ℕ} (hR : 0 < R) (hN : 0 < N)
    {x y : ℝ} (hx : |x| ≤ R) (hy : |y| ≤ R) (hxy : |x-y| ≤ 2 * width R N) :
    (realCell R N hN x).val ≤ (realCell R N hN y).val + 3 := by
  have h1 := (realCell_bounds hR hN x hx).1
  have h2 := (realCell_bounds hR hN y hy).2
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < width R N := by dsimp [width]; positivity
  have h := (abs_le.mp hxy).2
  have hmul : ((realCell R N hN x).val : ℝ) * width R N ≤
      ((realCell R N hN y).val + 3) * width R N := by nlinarith
  have := (mul_le_mul_iff_left₀ hw).mp hmul
  exact_mod_cast this

private theorem four_axis_values {ι : Type*} (S : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ S, ∀ j ∈ S, f i ≤ f j + 3) : (S.image f).card ≤ 4 := by
  classical
  by_cases hn : (S.image f).Nonempty
  · let m := (S.image f).min' hn
    have hm : m ∈ S.image f := min'_mem _ _
    obtain ⟨j,hj,hj'⟩ := mem_image.mp hm
    have sub : S.image f ⊆ Icc m (m+3) := by
      intro y hy
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
      exact mem_Icc.mpr ⟨min'_le _ _ (mem_image.mpr ⟨i,hi,rfl⟩), hj' ▸ h i hi j hj⟩
    exact (card_le_card sub).trans (by rw [Nat.card_Icc]; omega)
  · simp [not_nonempty_iff_eq_empty.mp hn]

private theorem sixteen_cells {ι : Type*} (S : Finset ι) (w : ι → ℂ)
    {R : ℝ} {N : ℕ} (hR : 0 < R) (hN : 0 < N)
    (bounded : ∀ i ∈ S, ‖w i‖ ≤ R)
    (diam : ∀ i ∈ S, ∀ j ∈ S, ‖w i - w j‖ ≤ 2 * width R N) :
    (S.image fun i => cell R N hN (w i)).card ≤ 16 := by
  classical
  let cp := fun i => cell R N hN (w i)
  let x := fun i => (cp i).1.val
  let y := fun i => (cp i).2.val
  have hx : (S.image x).card ≤ 4 := by
    apply four_axis_values
    intro i hi j hj
    exact axis_index_gap hR hN ((Complex.abs_re_le_norm _).trans (bounded i hi))
      ((Complex.abs_re_le_norm _).trans (bounded j hj))
      ((Complex.abs_re_le_norm (w i - w j)).trans (diam i hi j hj))
  have hy : (S.image y).card ≤ 4 := by
    apply four_axis_values
    intro i hi j hj
    exact axis_index_gap hR hN ((Complex.abs_im_le_norm _).trans (bounded i hi))
      ((Complex.abs_im_le_norm _).trans (bounded j hj))
      ((Complex.abs_im_le_norm (w i - w j)).trans (diam i hi j hj))
  apply (card_le_card_of_injOn (fun c : Cell N => (c.1.val, c.2.val))
    (t := (S.image x) ×ˢ (S.image y)) ?_ ?_).trans
  · rw [card_product]
    exact Nat.mul_le_mul hx hy
  · intro c hc
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hc
    exact mem_product.mpr ⟨mem_image.mpr ⟨i,hi,rfl⟩, mem_image.mpr ⟨i,hi,rfl⟩⟩
  · intro a _ b _ hab
    exact Prod.ext (Fin.ext (congrArg Prod.fst hab)) (Fin.ext (congrArg Prod.snd hab))

/-- Reciprocal differences contract when both denominators have norm at
least one. The center coordinates need not be conjugate after embedding. -/
theorem reciprocal_contraction (z₁ z₂ w₁ w₂ c d : ℂ)
    (h₁ : (z₁-c)*(w₁-d) = 1) (h₂ : (z₂-c)*(w₂-d) = 1)
    (hz₁ : 1 ≤ ‖z₁-c‖) (hz₂ : 1 ≤ ‖z₂-c‖) :
    ‖w₁-w₂‖ ≤ ‖z₁-z₂‖ := by
  have he : (w₁-w₂) * ((z₁-c)*(z₂-c)) = -(z₁-z₂) := by
    linear_combination (z₂-c)*h₁ - (z₁-c)*h₂
  have hn := congrArg norm he
  rw [norm_mul, norm_mul, norm_neg] at hn
  calc
    ‖w₁-w₂‖ ≤ ‖w₁-w₂‖ * (‖z₁-c‖ * ‖z₂-c‖) := by
      exact le_mul_of_one_le_right (norm_nonneg _) (one_le_mul_of_one_le_of_one_le hz₁ hz₂)
    _ = _ := hn

private theorem branch_count {ι : Type*} (S : Finset ι) (z w : ι → ℂ)
    {R : ℝ} {N : ℕ} (hR : 0 < R) (hN : 0 < N)
    (hb : ∀ i ∈ S, ‖z i‖ ≤ R ∧ ‖w i‖ ≤ R)
    (lip : ∀ i ∈ S, ∀ j ∈ S, ‖w i-w j‖ ≤ ‖z i-z j‖) :
    (S.image fun i => (cell R N hN (z i), cell R N hN (w i))).card ≤ 16 * N^2 := by
  classical
  let cz i := cell R N hN (z i)
  let cw i := cell R N hN (w i)
  let pairs := S.image fun i => (cz i, cw i)
  have hf (c : Cell N) : (pairs.filter fun v => v.1 = c).card ≤ 16 := by
    let U := S.filter fun i => cz i = c
    have hbU (i) (hi : i ∈ U) : ‖w i‖ ≤ R := (hb i (mem_filter.mp hi).1).2
    have hdr (i) (hi : i ∈ U) (j) (hj : j ∈ U) : ‖w i-w j‖ ≤ 2 * width R N := by
      obtain ⟨hi₁,hi₂⟩ := mem_filter.mp hi
      obtain ⟨hj₁,hj₂⟩ := mem_filter.mp hj
      exact (lip i hi₁ j hj₁).trans (same_cell_near hR hN (hb i hi₁).1
        (hb j hj₁).1 (hi₂.trans hj₂.symm))
    apply (card_le_card_of_injOn Prod.snd (t := U.image cw) ?_ ?_).trans
      (sixteen_cells U w hR hN hbU hdr)
    · intro v hv
      obtain ⟨hv', hvc⟩ := mem_filter.mp hv
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hv'
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨hi,hvc⟩,rfl⟩
    · intro a ha b hb' he
      exact Prod.ext ((mem_filter.mp ha).2.trans (mem_filter.mp hb').2.symm) he
  calc
    pairs.card = ∑ c : Cell N, (pairs.filter fun v => v.1 = c).card :=
      card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
    _ ≤ ∑ _ : Cell N, 16 := sum_le_sum (fun c _ => hf c)
    _ = 16 * N^2 := by simp [Cell, pow_two, Nat.mul_comm]

/-- The bounded four-index codes occupied by actual neighbors. -/
def boundedCells {ι : Type*} (S : Finset ι) (z w : ι → ℂ) (R : ℝ) (N : ℕ)
    (hN : 0 < N) : Finset (Cell N × Cell N) :=
  (S.filter fun i => ‖z i‖ ≤ R ∧ ‖w i‖ ≤ R).image
    fun i => (cell R N hN (z i), cell R N hN (w i))

/-- Bounded center acceptance consists of the distinct bounded neighbor
codes together with overflow. -/
def accepted {ι : Type*} (S : Finset ι) (z w : ι → ℂ) (R : ℝ) (N : ℕ)
    (hN : 0 < N) : Finset (Option (Cell N × Cell N)) :=
  insert none ((boundedCells S z w R N hN).image some)

/-- The actual point code used in the test: either of the two complex norms
exceeding R triggers the single common overflow symbol. -/
def code (R : ℝ) (N : ℕ) (hN : 0 < N) (z w : ℂ) : Option (Cell N × Cell N) :=
  if ‖z‖ ≤ R ∧ ‖w‖ ≤ R then some (cell R N hN z, cell R N hN w) else none

theorem code_mem_accepted {ι : Type*} (S : Finset ι) (z w : ι → ℂ)
    (R : ℝ) (N : ℕ) (hN : 0 < N) {i : ι} (hi : i ∈ S) :
    code R N hN (z i) (w i) ∈ accepted S z w R N hN := by
  classical
  by_cases hb : ‖z i‖ ≤ R ∧ ‖w i‖ ≤ R
  · rw [code, if_pos hb]
    apply mem_insert_of_mem
    exact mem_image.mpr ⟨_, mem_image.mpr ⟨i,mem_filter.mpr ⟨hi,hb⟩,rfl⟩,rfl⟩
  · simp [code, hb, accepted]

/-- The real and imaginary parts of each bounded coordinate give four
indices in Fin N, beside one common overflow symbol. -/
theorem alphabet_card (N : ℕ) : Fintype.card (Option (Cell N × Cell N)) = N^4+1 := by
  simp [Cell]; ring

/-- Sharp bookkeeping of the manuscript's test alphabet. -/
theorem accepted_card_le {ι : Type*} (S : Finset ι) (z w : ι → ℂ) (c d : ℂ)
    {R : ℝ} {N : ℕ} (hR : 0 < R) (hN : 0 < N)
    (true_edge : ∀ i ∈ S, (z i-c)*(w i-d) = 1) :
    (accepted S z w R N hN).card ≤ 32*N^2+1 := by
  classical
  let S₀ := S.filter fun i => ‖z i‖ ≤ R ∧ ‖w i‖ ≤ R
  let U := S₀.filter fun i => 1 ≤ ‖z i-c‖
  let V := S₀.filter fun i => ¬ 1 ≤ ‖z i-c‖
  let f i := (cell R N hN (z i), cell R N hN (w i))
  have uf : (U.image f).card ≤ 16*N^2 := by
    apply branch_count U z w hR hN
    · intro i hi; exact (mem_filter.mp (mem_filter.mp hi).1).2
    · intro i hi j hj
      exact reciprocal_contraction _ _ _ _ _ _ (true_edge i (mem_filter.mp (mem_filter.mp hi).1).1)
        (true_edge j (mem_filter.mp (mem_filter.mp hj).1).1) (mem_filter.mp hi).2 (mem_filter.mp hj).2
  have flip (i) (hi : i ∈ V) : 1 ≤ ‖w i-d‖ := by
    obtain ⟨hi₀,hz⟩ := mem_filter.mp hi
    have h := congrArg norm (true_edge i (mem_filter.mp hi₀).1)
    rw [norm_mul, norm_one] at h
    by_contra! hw
    have ht := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hz)) (norm_nonneg (w i-d))
    rw [one_mul] at ht
    linarith
  have vv : (V.image fun i => (f i).swap).card ≤ 16*N^2 := by
    apply branch_count V w z hR hN
    · intro i hi; exact (mem_filter.mp (mem_filter.mp hi).1).2.symm
    · intro i hi j hj
      exact reciprocal_contraction _ _ _ _ _ _ ((mul_comm _ _).trans
        (true_edge i (mem_filter.mp (mem_filter.mp hi).1).1)) ((mul_comm _ _).trans
        (true_edge j (mem_filter.mp (mem_filter.mp hj).1).1)) (flip i hi) (flip j hj)
  have vf : (V.image f).card ≤ 16*N^2 := by
    rw [← card_image_of_injective (V.image f) (f := Prod.swap) Prod.swap_injective]
    simpa [Finset.image_image, Function.comp_def] using vv
  have split : S₀ = U ∪ V := (filter_union_filter_not_eq _ _).symm
  have hc : (boundedCells S z w R N hN).card ≤ 32*N^2 := by
    change (S₀.image f).card ≤ _
    rw [split, image_union]
    exact (card_union_le _ _).trans (by omega)
  exact (card_insert_le _ _).trans
    (Nat.add_le_add_right ((card_image_le).trans hc) 1)

end PlanarUnitDistances.CircleCells
