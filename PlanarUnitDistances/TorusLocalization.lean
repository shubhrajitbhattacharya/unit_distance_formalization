import PlanarUnitDistances.GridLocalization
import PlanarUnitDistances.TorusRank

/-! A Jacobian velocity on the concrete torus is equivalently specified by
position velocities and logarithmic velocities of the units. Sparse localization
therefore applies to the concrete quadratic defining ideal. -/

noncomputable section

namespace PlanarUnitDistances.TorusCritical

open MvPolynomial CriticalLocus GridLocalization

variable {I J k : Type*} [Field k] [Fintype I] [Fintype J]

variable (p : I → k × k) (s : Option J → k × k) (a : I → Option J → kˣ)
  (i₀ : I) (sol : Fibre.TorusSolution i₀ none p s a)

def chordRatio (i : I) (j : Option J) : k := (↑(a i j * sol.row i * sol.col j) : k)

def chordRoot (i : I) (j : Option J) : k :=
  (chordRatio p s a i₀ sol i j)⁻¹ - chordRatio p s a i₀ sol i j

/-- Log velocities of a row unit and of a column unit are `u_i[2]` and
`−b_j` respectively. The inverse motions are then forced. -/
def gridVelocity (u : I → Fin 3 → k) (b : Shared k J) : Coord I J → k
  | .inl (i,h) => ![u i 0, u i 1, (sol.row i : k) * u i 2, -(↑(sol.row i)⁻¹ : k) * u i 2] h
  | .inr (.inl (j,h)) => b.1 (j,h)
  | .inr (.inr (j,h)) => ![-(sol.col (some j) : k) * b.2 j, (↑(sol.col (some j))⁻¹ : k) * b.2 j] h

theorem ratio_velocity (u : I → Fin 3 → k) (b : Shared k J) (i : I) (j : Option J) :
    jacobianRow (coordinates p s a i₀ sol) (ratio a i j) (gridVelocity p s a i₀ sol u b) =
      chordRatio p s a i₀ sol i j * (u i 2 - colLog b j) := by
  cases j <;> simp [ratio, derivative_mul, derivative_constant, derivative_variable, colUnit, colLog, gridVelocity, coordinates,
    chordRatio, sol.base_col] <;> ring

theorem gridVelocity_in_kernel (u : I → Fin 3 → k) (b : Shared k J)
    (he : ∀ i j, rowEquation p s (chordRoot p s a i₀ sol) i (u i) b j) (e : Equation I J) :
    jacobianRow (coordinates p s a i₀ sol) (equation a e) (gridVelocity p s a i₀ sol u b) = 0 := by
  have hone : jacobianRow (coordinates p s a i₀ sol) (1 : Poly I J k) (gridVelocity p s a i₀ sol u b) = 0 :=
    derivative_constant _ _ 1
  rcases e with i | (j | ⟨i,j⟩)
  · simp [equation, derivative_sub, derivative_mul, derivative_variable, hone, gridVelocity, coordinates]
    field_simp
    ring
  · simp [equation, derivative_sub, derivative_mul, derivative_variable, hone, colUnit, gridVelocity, coordinates]
    field_simp
    ring
  · have h := he i j
    cases j <;> simp [equation, derivative_add, derivative_sub, derivative_mul, derivative_constant, derivative_variable, positionDifference, pow_two,
      ratio, inverseRatio, colUnit, coordinates, gridVelocity, rowEquation, chordRoot, chordRatio,
      colLog, sol.base_col] at h ⊢ <;> linear_combination h

/-- Start from the kernel of the explicit full Jacobian. Retain at most
`3l−3` rows and force the same target logarithmic derivative to vanish for
every solution of the restricted first-order equations. -/
theorem localize_stationary_ratio [Nontrivial I]
    (iₑ : I) (jₑ j j' : Option J) (hj : s j ≠ s j')
    (hs : ∀ v : Coord I J → k,
      (∀ e, jacobianRow (coordinates p s a i₀ sol) (equation a e) v = 0) →
      jacobianRow (coordinates p s a i₀ sol) (ratio a iₑ jₑ) v = 0) :
    ∃ S : Finset I, iₑ ∈ S ∧ 2 ≤ S.card ∧ S.card ≤ 3 * Fintype.card (Option J) - 3 ∧
      ∀ (b : Shared k J) (u : I → Fin 3 → k),
        (∀ i ∈ S, ∀ q, rowEquation p s (chordRoot p s a i₀ sol) i (u i) b q) →
          u iₑ 2 - colLog b jₑ = 0 := by
  apply localize_logarithmic_tangent p s _ iₑ jₑ j j' hj
  intro b u hfull
  have hm := hs _ (gridVelocity_in_kernel p s a i₀ sol u b hfull)
  rw [ratio_velocity] at hm
  exact (mul_eq_zero.mp hm).resolve_left (Units.ne_zero _)

end PlanarUnitDistances.TorusCritical
