import PlanarUnitDistances.TorusLocalization

/-! Localization directly on the Jacobian of the restricted, renormalized torus. -/

noncomputable section

namespace PlanarUnitDistances.TorusCritical

open MvPolynomial CriticalLocus GridLocalization

variable {I J k : Type*} [Field k] [Fintype I] [Fintype J]
variable (p : I → k × k) (s : Option J → k × k) (a : I → Option J → kˣ)
  (i₀ : I) (sol : Fibre.TorusSolution i₀ none p s a)

def readLocal (v : Coord I J → k) (i : I) : Fin 3 → k :=
  ![v (.inl (i,0)), v (.inl (i,1)), (↑(sol.row i)⁻¹ : k) * v (.inl (i,2))]

def readShared (v : Coord I J → k) : Shared k J :=
  (fun q ↦ v (.inr (.inl q)), fun j ↦ -(↑(sol.col (some j))⁻¹ : k) * v (.inr (.inr (j,0))))

/-- An arbitrary Jacobian velocity reconstructs exactly from its logarithmic
unit velocities. The two inverse-coordinate derivatives are forced by the
inverse equations. -/
theorem reconstruct_velocity (v : Coord I J → k)
    (hv : ∀ e, jacobianRow (coordinates p s a i₀ sol) (equation a e) v = 0) :
    gridVelocity p s a i₀ sol (readLocal p s a i₀ sol v) (readShared p s a i₀ sol v) = v := by
  have hone : jacobianRow (coordinates p s a i₀ sol) (1 : Poly I J k) v = 0 := derivative_constant _ _ 1
  funext c
  rcases c with ⟨i,h⟩ | (⟨j,h⟩ | ⟨j,h⟩)
  · have hi := hv (.inl i)
    simp [equation, derivative_sub, derivative_mul, derivative_variable, hone, coordinates] at hi
    fin_cases h <;> simp [gridVelocity, readLocal, ← mul_assoc]
    field_simp at hi ⊢
    linear_combination -hi
  · rfl
  · have hj := hv (.inr (.inl j))
    simp [equation, derivative_sub, derivative_mul, derivative_variable, hone, colUnit, coordinates] at hj
    fin_cases h <;> simp [gridVelocity, readShared, ← mul_assoc]
    field_simp at hj ⊢
    linear_combination -hj

theorem kernel_implies_rowEquation (v : Coord I J → k)
    (hv : ∀ e, jacobianRow (coordinates p s a i₀ sol) (equation a e) v = 0)
    (i : I) (j : Option J) :
    rowEquation p s (chordRoot p s a i₀ sol) i (readLocal p s a i₀ sol v i)
      (readShared p s a i₀ sol v) j := by
  let u := readLocal p s a i₀ sol v
  let b := readShared p s a i₀ sol v
  change rowEquation _ _ _ _ (u i) b _
  have hh := hv (.inr (.inr (i,j)))
  rw [← reconstruct_velocity p s a i₀ sol v hv] at hh
  change jacobianRow _ _ (gridVelocity p s a i₀ sol u b) = 0 at hh
  cases j <;> simp [equation, derivative_add, derivative_sub, derivative_mul, derivative_constant,
    derivative_variable, positionDifference, pow_two, ratio, inverseRatio, colUnit, coordinates,
    gridVelocity, rowEquation, chordRoot, chordRatio, colLog, sol.base_col] at hh ⊢ <;> linear_combination hh

variable (S : Finset I) (b₀ : S)

def restrictedCoefficient (i : S) (j : Option J) : kˣ := a i j / a b₀ j

private theorem rescale_unit (a b u v : kˣ) : a / b * u * (b * v) = a * u * v := by
  rw [div_eq_mul_inv]
  calc
    _ = a * u * (b⁻¹ * b) * v := by ac_rfl
    _ = _ := by simp

/-- Retain all columns, normalize at a retained row and absorb the old base
row's factor into each column unit. The represented ratios stay equal. -/
def restrictedSolution (ha : ∀ i, a i none = 1) :
    Fibre.TorusSolution b₀ none (fun i : S ↦ p i) s (restrictedCoefficient a S b₀) where
  row i := sol.row i
  col j := a b₀ j * sol.col j
  base_col := by simp [ha, sol.base_col]
  distance i j := by
    have he : restrictedCoefficient a S b₀ i j * sol.row i * (a b₀ j * sol.col j) =
        a i j * sol.row i * sol.col j := by
      exact rescale_unit _ _ _ _
    rw [he]
    exact sol.distance i j

omit [Fintype I] [Fintype J] in
theorem restricted_chordRatio (ha : ∀ i, a i none = 1) (i : S) (j : Option J) :
    chordRatio (fun i : S ↦ p i) s (restrictedCoefficient a S b₀) b₀
      (restrictedSolution p s a i₀ sol S b₀ ha) i j = chordRatio p s a i₀ sol i j := by
  unfold chordRatio
  apply congrArg Units.val
  change a i j / a b₀ j * sol.row i * (a b₀ j * sol.col j) = _
  exact rescale_unit _ _ _ _


omit S b₀ in
/-- Manuscript sparse localization on the actual full and normalized subgrid
Jacobian kernels. The selected grid retains the target and all columns. -/
theorem sparse_subgrid [Nontrivial I] (ha : ∀ i, a i none = 1)
    (iₑ : I) (jₑ j j' : Option J) (hj : s j ≠ s j')
    (hs : ∀ v : Coord I J → k,
      (∀ e, jacobianRow (coordinates p s a i₀ sol) (equation a e) v = 0) →
      jacobianRow (coordinates p s a i₀ sol) (ratio a iₑ jₑ) v = 0) :
    ∃ (S : Finset I) (hi : iₑ ∈ S), 2 ≤ S.card ∧ S.card ≤ 3 * Fintype.card (Option J) - 3 ∧
      ∀ b₀ : S, let β := restrictedCoefficient a S b₀
        let y := coordinates (fun i : S ↦ p i) s β b₀ (restrictedSolution p s a i₀ sol S b₀ ha)
        ∀ v : Coord S J → k, (∀ e, jacobianRow y (equation β e) v = 0) →
          jacobianRow y (ratio β ⟨iₑ,hi⟩ jₑ) v = 0 := by
  classical
  obtain ⟨S, hi, hsmall, hlarge, hlog⟩ := localize_stationary_ratio p s a i₀ sol iₑ jₑ j j' hj hs
  refine ⟨S, hi, hsmall, hlarge, ?_⟩
  intro b₀
  let β := restrictedCoefficient a S b₀
  let q := fun i : S ↦ p i
  let small := restrictedSolution p s a i₀ sol S b₀ ha
  change ∀ v : Coord S J → k, (∀ e, jacobianRow (coordinates q s β b₀ small) (equation β e) v = 0) →
    jacobianRow (coordinates q s β b₀ small) (ratio β ⟨iₑ,hi⟩ jₑ) v = 0
  intro v hv
  let u := readLocal q s β b₀ small v
  let b := readShared q s β b₀ small v
  let u' (i : I) := if hi : i ∈ S then u ⟨i,hi⟩ else 0
  have hsmallRoot (i : S) (j : Option J) : chordRoot q s β b₀ small i j = chordRoot p s a i₀ sol i j := by
    simp only [chordRoot, q, β, small, restricted_chordRatio]
  have hrows (i : I) (hi' : i ∈ S) (j : Option J) :
      rowEquation p s (chordRoot p s a i₀ sol) i (u' i) b j := by
    have he := kernel_implies_rowEquation q s β b₀ small v hv ⟨i,hi'⟩ j
    simpa only [rowEquation, hsmallRoot, q, u', dif_pos hi', u, b] using he
  have hzero := hlog b u' hrows
  have h' : u ⟨iₑ,hi⟩ 2 - colLog b jₑ = 0 := by simpa [u', hi] using hzero
  change jacobianRow (coordinates q s β b₀ small) (ratio β ⟨iₑ,hi⟩ jₑ) v = 0
  rw [← reconstruct_velocity q s β b₀ small v hv, ratio_velocity]
  exact mul_eq_zero_of_right _ h'

end PlanarUnitDistances.TorusCritical
