import Mathlib.Algebra.DualNumber
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! First-order equations of the fixed-quotient fibre. A point with coordinates in the dual numbers records a point and
a scheme tangent vector, even on a singular or nonreduced fibre. -/

namespace PlanarUnitDistances.Fibre

open TrivSqZeroExt

variable {K : Type*} [Field K]
variable {I J : Type*}

/-- The squared distance uses the bilinear extension of the real Euclidean form. -/
def chordSq {R : Type*} [CommRing R] (p r : R × R) : R :=
  (p.1 - r.1) ^ 2 + (p.2 - r.2) ^ 2

/-- Logarithmic derivative of a dual number whose constant term is nonzero. -/
def logVelocity (u : DualNumber K) : K := u.snd / u.fst

private theorem logVelocity_mul (u v : DualNumber K) (hu : u.fst ≠ 0) (hv : v.fst ≠ 0) :
    logVelocity (u * v) = logVelocity u + logVelocity v := by
  simp only [logVelocity, DualNumber.snd_mul, fst_mul]
  field_simp
  ring

/-- The three defining equations on a grid. The constant-quotient equations can
be written on every index by setting the base row and column of the coefficients
equal to one. Their redundant boundary equations then hold identically. -/
structure GridEquations {R : Type*} [CommRing R] (i₀ : I) (j₀ : J)
    (p : I → R × R) (r : J → R × R) (u m a : I → J → R) : Prop where
  distance : ∀ i j, chordSq (p i) (r j) = 2 - u i j - m i j
  inverse : ∀ i j, u i j * m i j = 1
  rect : ∀ i j, u i j * u i₀ j₀ = a i j * (u i j₀ * u i₀ j)

def position (v : DualNumber K × DualNumber K) : K × K := (v.1.fst, v.2.fst)

def velocity (v : DualNumber K × DualNumber K) : K × K := (v.1.snd, v.2.snd)

def dot (v w : K × K) : K := v.1 * w.1 + v.2 * w.2

private theorem chordSq_fst (p r : DualNumber K × DualNumber K) :
    (chordSq p r).fst = chordSq (position p) (position r) := by
  simp [chordSq, position, pow_two]

private theorem chordSq_snd (p r : DualNumber K × DualNumber K) :
    (chordSq p r).snd = 2 * dot (position p - position r) (velocity p - velocity r) := by
  simp only [chordSq, position, velocity, dot, Prod.fst_sub, Prod.snd_sub, pow_two,
    snd_add, DualNumber.snd_mul, fst_sub, snd_sub]
  ring

/-- Each rectangle has fixed coefficient in the ground field, so its first
derivative vanishes. Hence the logarithmic velocities split as row minus column.
The statement and proof do not require distinct positions or smoothness. -/
theorem moving_grid_differential (i₀ : I) (j₀ : J)
    (p : I → DualNumber K × DualNumber K) (r : J → DualNumber K × DualNumber K)
    (u m : I → J → DualNumber K) (a : I → J → K)
    (h : GridEquations i₀ j₀ p r u m (fun i j => inl (a i j)))
    (moving : ∀ i j, (u i j).snd ≠ 0) :
    ∃ (A : I → K) (b : J → K), ∀ i j,
      let L := chordSq (position (p i)) (position (r j))
      let R := (m i j).fst - (u i j).fst
      2 * dot (position (p i) - position (r j)) (velocity (p i) - velocity (r j)) =
        R * (A i - b j) ∧ R ^ 2 = L * (L - 4) ∧ A i - b j ≠ 0 := by
  have inv₀ (i : I) (j : J) : (u i j).fst * (m i j).fst = 1 := by
    simpa only [fst_mul, fst_one] using congrArg fst (h.inverse i j)
  have hu (i : I) (j : J) : (u i j).fst ≠ 0 := left_ne_zero_of_mul_eq_one (inv₀ i j)
  have ha (i : I) (j : J) : a i j ≠ 0 := by
    have hh := congrArg fst (h.rect i j)
    simp only [fst_mul, fst_inl] at hh
    intro hz
    rw [hz, zero_mul] at hh
    exact (mul_ne_zero (hu i j) (hu i₀ j₀)) hh
  refine ⟨fun i => logVelocity (u i j₀), fun j => logVelocity (u i₀ j₀) -
    logVelocity (u i₀ j), ?_⟩
  intro i j
  dsimp only
  have hv := congrArg logVelocity (h.rect i j)
  rw [logVelocity_mul _ _ (hu i j) (hu i₀ j₀),
    logVelocity_mul (inl (a i j)) (u i j₀ * u i₀ j) (ha i j)
      (by rw [fst_mul]; exact mul_ne_zero (hu i j₀) (hu i₀ j)),
    logVelocity_mul _ _ (hu i j₀) (hu i₀ j)] at hv
  simp only [logVelocity, snd_inl, fst_inl, zero_div, zero_add] at hv
  have split : logVelocity (u i j₀) - (logVelocity (u i₀ j₀) - logVelocity (u i₀ j)) =
      logVelocity (u i j) := by dsimp [logVelocity]; linear_combination -hv
  rw [split]
  have dist₀ := congrArg fst (h.distance i j)
  have dist₁ := congrArg snd (h.distance i j)
  have inv₁ := congrArg snd (h.inverse i j)
  have hf₂ : (2 : DualNumber K).fst = 2 := rfl
  have hs₂ : (2 : DualNumber K).snd = 0 := rfl
  simp only [chordSq_fst, fst_sub, hf₂] at dist₀
  simp only [chordSq_snd, snd_sub, hs₂, zero_sub] at dist₁
  simp only [DualNumber.snd_mul, snd_one] at inv₁
  refine ⟨?_, ?_, div_ne_zero (moving i j) (hu i j)⟩
  · rw [dist₁, logVelocity]
    field_simp [hu]
    linear_combination -inv₁
  · rw [dist₀]
    linear_combination -4 * inv₀ i j

/-- The dual-number lift of a position with specified velocity. -/
def liftPosition (p H : K × K) : DualNumber K × DualNumber K :=
  ((p.1, H.1), (p.2, H.2))

/-- A ratio with prescribed infinitesimal increment. -/
def liftScalar (x dx : K) : DualNumber K := (x, dx)

/-- The displayed first-order equations suffice for a tangent of the original
fibre. In particular the row and column scalar representation loses no
information. The proof constructs the lifts of both the ratios and inverses. -/
theorem lift_differential (i₀ : I) (j₀ : J) (p H : I → K × K) (r U : J → K × K)
    (u m a : I → J → K) (A : I → K) (b : J → K)
    (h : GridEquations i₀ j₀ p r u m a)
    (diff : ∀ i j, 2 * dot (p i - r j) (H i - U j) = (m i j - u i j) * (A i - b j)) :
    GridEquations i₀ j₀ (fun i => liftPosition (p i) (H i)) (fun j => liftPosition (r j) (U j))
      (fun i j => liftScalar (u i j) (u i j * (A i - b j)))
      (fun i j => liftScalar (m i j) (-m i j * (A i - b j)))
      (fun i j => inl (a i j)) := by
  have hf₂ : (2 : DualNumber K).fst = 2 := rfl
  have hs₂ : (2 : DualNumber K).snd = 0 := rfl
  constructor
  · intro i j
    apply TrivSqZeroExt.ext
    · rw [chordSq_fst, fst_sub, fst_sub, hf₂]
      exact h.distance i j
    · rw [chordSq_snd, snd_sub, snd_sub, hs₂]
      change 2 * dot (p i - r j) (H i - U j) =
        0 - u i j * (A i - b j) - -m i j * (A i - b j)
      rw [diff]
      ring
  · intro i j
    apply TrivSqZeroExt.ext
    · exact h.inverse i j
    · simp only [DualNumber.snd_mul, snd_one]
      change u i j * (-m i j * (A i - b j)) + u i j * (A i - b j) * m i j = 0
      ring
  · intro i j
    apply TrivSqZeroExt.ext
    · exact h.rect i j
    · simp only [DualNumber.snd_mul, fst_mul, fst_inl, snd_inl, zero_mul,
        add_zero]
      simp only [liftScalar, fst_mk, snd_mk]
      linear_combination (A i + A i₀ - b j - b j₀) * h.rect i j


section Torus

variable {R : Type*} [CommRing R]

/-- The reduced system of equations in the row and column torus parameters. Units implement the inverse equations exactly. -/
@[ext] structure TorusSolution (i₀ : I) (j₀ : J) (p : I → R × R) (r : J → R × R)
    (a : I → J → Rˣ) where
  row : I → Rˣ
  col : J → Rˣ
  base_col : col j₀ = 1
  distance : ∀ i j, chordSq (p i) (r j) =
    2 - ↑(a i j * row i * col j) - ↑((a i j * row i * col j)⁻¹)

/-- The fixed-quotient equations, with ratios valued in the unit group of the
test ring. The inverse coordinate of each ratio is uniquely prescribed. -/
@[ext] structure RatioSolution (i₀ : I) (j₀ : J) (p : I → R × R) (r : J → R × R)
    (a : I → J → Rˣ) where
  ratio : I → J → Rˣ
  distance : ∀ i j, chordSq (p i) (r j) = 2 - ↑(ratio i j) - ↑((ratio i j)⁻¹)
  rect : ∀ i j, ratio i j * ratio i₀ j₀ = a i j * (ratio i j₀ * ratio i₀ j)

/-- The torus-to-ratio parametrization and its inverse work over every
commutative test ring, hence also over rings carrying nilpotent elements.
The two maps leave all position coordinates fixed. -/
def torusEquivRatio (i₀ : I) (j₀ : J) (p : I → R × R) (r : J → R × R)
    (a : I → J → Rˣ) (base_row : ∀ j, a i₀ j = 1) (base_col : ∀ i, a i j₀ = 1) :
    TorusSolution i₀ j₀ p r a ≃ RatioSolution i₀ j₀ p r a where
  toFun t :=
    { ratio := fun i j => a i j * t.row i * t.col j
      distance := t.distance
      rect := by
        intro i j
        simp only [base_row, base_col, t.base_col, one_mul, mul_one]
        ac_rfl }
  invFun l :=
    { row := fun i => l.ratio i j₀
      col := fun j => l.ratio i₀ j / l.ratio i₀ j₀
      base_col := div_self' _
      distance := by
        intro i j
        have he : a i j * l.ratio i j₀ * (l.ratio i₀ j / l.ratio i₀ j₀) = l.ratio i j := by
          rw [← mul_div_assoc, div_eq_iff_eq_mul]
          simpa only [mul_assoc] using (l.rect i j).symm
        rw [he]
        exact l.distance i j }
  left_inv t := by
    apply TorusSolution.ext
    · funext i
      simp [base_col, t.base_col]
    · funext j
      simp [base_row, t.base_col, mul_comm]
  right_inv l := by
    apply RatioSolution.ext
    funext i j
    change a i j * l.ratio i j₀ * (l.ratio i₀ j / l.ratio i₀ j₀) = l.ratio i j
    rw [← mul_div_assoc, div_eq_iff_eq_mul]
    simpa only [mul_assoc] using (l.rect i j).symm


end Torus

end PlanarUnitDistances.Fibre
