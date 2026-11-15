import PlanarUnitDistances.Algebra
import PlanarUnitDistances.CriticalLocus

/-! The multiplier construction for the manuscript's normalized torus grid.
Columns are indexed by `Option J`: the base column is `none` and its torus
coordinates are the constants 1. -/

noncomputable section

namespace PlanarUnitDistances.TorusCritical

open MvPolynomial
open CriticalLocus

variable {I J k : Type*} [Field k]

abbrev Coord (I J : Type*) := (I × Fin 4) ⊕ ((Option J × Fin 2) ⊕ (J × Fin 2))
abbrev Equation (I J : Type*) := I ⊕ (J ⊕ (I × Option J))
abbrev Poly (I J k : Type*) [Field k] := MvPolynomial (Coord I J) k

def colUnit (j : Option J) (h : Fin 2) : Poly I J k :=
  j.elim 1 (fun s ↦ X (.inr (.inr (s, h))))

def positionDifference (i : I) (j : Option J) (h : Fin 2) : Poly I J k :=
  X (.inl (i, h.castLE (by decide))) - X (.inr (.inl (j, h)))

def ratio (a : I → Option J → kˣ) (i : I) (j : Option J) : Poly I J k :=
  C (a i j : k) * X (.inl (i, 2)) * colUnit j 0

def inverseRatio (a : I → Option J → kˣ) (i : I) (j : Option J) : Poly I J k :=
  C (↑(a i j)⁻¹ : k) * X (.inl (i, 3)) * colUnit j 1

def equation (a : I → Option J → kˣ) : Equation I J → Poly I J k
  | .inl i => X (.inl (i, 2)) * X (.inl (i, 3)) - 1
  | .inr (.inl j) => colUnit (some j) 0 * colUnit (some j) 1 - 1
  | .inr (.inr (i,j)) => positionDifference i j 0 ^ 2 + positionDifference i j 1 ^ 2
      - C (2 : k) + ratio a i j + inverseRatio a i j

private theorem colUnit_degree (j : Option J) (h : Fin 2) :
    (colUnit (I := I) (k := k) j h).totalDegree ≤ 1 := by
  cases j <;> simp [colUnit]

private theorem positionDifference_degree (i : I) (j : Option J) (h : Fin 2) :
    (positionDifference (k := k) i j h).totalDegree ≤ 1 := by
  exact (totalDegree_sub _ _).trans (by simp)

private theorem term_degree (a : k) (u : Coord I J) (j : Option J) (h : Fin 2) :
    (C a * X u * colUnit j h).totalDegree ≤ 2 := by
  apply (totalDegree_mul _ _).trans
  have h1 := totalDegree_mul (C a) (X u)
  rw [totalDegree_C, totalDegree_X] at h1
  have h2 := colUnit_degree (I := I) (k := k) j h
  omega

theorem ratio_degree (a : I → Option J → kˣ) (i : I) (j : Option J) :
    (ratio a i j).totalDegree ≤ 2 :=
  term_degree _ _ _ _

theorem equation_degree (a : I → Option J → kˣ) (e : Equation I J) :
    (equation a e).totalDegree ≤ 2 := by
  rcases e with i | (j | ⟨i,j⟩)
  · apply (totalDegree_sub _ _).trans
    apply max_le _ (by simp)
    exact (totalDegree_mul _ _).trans (by simp)
  · apply (totalDegree_sub _ _).trans
    apply max_le _ (by simp)
    exact (totalDegree_mul _ _).trans (by simp [colUnit])
  · have hs (h : Fin 2) : (positionDifference (k := k) i j h ^ 2).totalDegree ≤ 2 :=
      (totalDegree_pow _ _).trans (by have := positionDifference_degree (k := k) i j h; omega)
    apply (totalDegree_add _ _).trans (max_le _ (term_degree _ _ _ _))
    apply (totalDegree_add _ _).trans (max_le _ (ratio_degree a i j))
    apply (totalDegree_sub _ _).trans (max_le _ (by simp))
    exact (totalDegree_add _ _).trans (max_le (hs 0) (hs 1))

variable (p : I → k × k) (s : Option J → k × k) (a : I → Option J → kˣ)
  (i₀ : I) (sol : Fibre.TorusSolution i₀ none p s a)

/-- Evaluation at an actual torus solution in the positions, units, and inverses. -/
def coordinates : Coord I J → k
  | .inl (i,h) => ![(p i).1, (p i).2, (sol.row i : k), (↑(sol.row i)⁻¹ : k)] h
  | .inr (.inl (j,h)) => ![(s j).1, (s j).2] h
  | .inr (.inr (j,h)) => ![(sol.col (some j) : k), (↑(sol.col (some j))⁻¹ : k)] h

private theorem evaluate_colUnit (j : Option J) :
    eval (coordinates p s a i₀ sol) (colUnit (k := k) j 0) = (sol.col j : k) ∧
    eval (coordinates p s a i₀ sol) (colUnit (k := k) j 1) = (↑(sol.col j)⁻¹ : k) := by
  cases j with
  | none => simp [colUnit, sol.base_col]
  | some j => simp [colUnit, coordinates]

theorem evaluate_ratio (i : I) (j : Option J) :
    aeval (coordinates p s a i₀ sol) (ratio a i j) = (↑(a i j * sol.row i * sol.col j) : k) := by
  simp [ratio, (evaluate_colUnit p s a i₀ sol j).1, coordinates]

theorem evaluate_equation (e : Equation I J) :
    aeval (coordinates p s a i₀ sol) (equation a e) = 0 := by
  rcases e with i | (j | ⟨i,j⟩)
  · simp [equation, coordinates]
  · simp [equation, (evaluate_colUnit p s a i₀ sol (some j)).1,
      (evaluate_colUnit p s a i₀ sol (some j)).2]
  · have hz := sol.distance i j
    simp [Fibre.chordSq, mul_inv_rev] at hz
    simp [equation, positionDifference, coordinates, ratio, inverseRatio,
      (evaluate_colUnit p s a i₀ sol j).1, (evaluate_colUnit p s a i₀ sol j).2]
    linear_combination hz

/-- The stationary chord ratio belongs to a constant-output irreducible component
through the specified grid. The ideal uses every explicit torus equation, even
when its corresponding row did not receive a multiplier. -/
theorem stationary_ratio_component [CharZero k] [IsAlgClosed k] [Fintype I] [Fintype J]
    (i : I) (j : Option J)
    (hs : ∀ v : Coord I J → k,
      (∀ e, jacobianRow (coordinates p s a i₀ sol) (equation a e) v = 0) →
      jacobianRow (coordinates p s a i₀ sol) (ratio a i j) v = 0) :
    ∃ (r : ℕ) (pick : Fin r → Equation I J) (t : Fin r → k),
      r = Module.finrank k (Submodule.span k (Set.range
        (fun e ↦ jacobianRow (coordinates p s a i₀ sol) (equation a e)))) ∧
      LinearIndependent k (fun u ↦ jacobianRow (coordinates p s a i₀ sol) (equation a (pick u))) ∧
      ∃ P ∈ (incidenceIdeal (ratio a i j) (equation a) pick).minimalPrimes,
        P ≤ RingHom.ker (aeval (liftedPoint (coordinates p s a i₀ sol) t
          (↑(a i j * sol.row i * sol.col j) : k))) ∧
        outputVariable - C (↑(a i j * sol.row i * sol.col j) : k) ∈ P ∧
        ∀ eqn, (incidenceEquation (ratio a i j) (equation a) pick eqn).totalDegree ≤ 2 := by
  obtain ⟨r, pick, t, hr, hi, P, hP, hlift, c, hc, hval⟩ :=
    stationary_coordinate_component (coordinates p s a i₀ sol) (ratio a i j) (equation a)
      (evaluate_equation p s a i₀ sol) hs
  rw [evaluate_ratio] at hlift hval
  change _ = c at hval
  refine ⟨r, pick, t, hr, hi, P, hP, hlift, hval ▸ hc, ?_⟩
  exact incidenceEquation_quadratic _ _ _ (ratio_degree a i j) (equation_degree a)

end PlanarUnitDistances.TorusCritical
