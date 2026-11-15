import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Reciprocal coordinates of a Euclidean unit edge and the first obstruction
for the convex unit ball x² + |y| ≤ 1. -/
namespace PlanarUnitDistances.EuclideanIdentity


/-- The two coordinate products are one on the two edges incident to a
common center. Both chord identities follow in any field. -/
theorem chord {K : Type*} [Field K] {d e D E : K} (hd : d*D=1) (he : e*E=1) :
    let ratio := d/e
    let L := (d-e)*(D-E)
    L = 2-ratio-ratio⁻¹ ∧ (ratio⁻¹-ratio)^2 = L*(L-4) := by
  have hd' : d ≠ 0 := by intro h; simp [h] at hd
  have he' : e ≠ 0 := by intro h; simp [h] at he
  have hD : D = d⁻¹ := by apply mul_left_cancel₀ hd'; simpa [hd'] using hd
  have hE : E = e⁻¹ := by apply mul_left_cancel₀ he'; simpa [he'] using he
  subst D
  subst E
  dsimp
  constructor <;> field_simp <;> ring

end PlanarUnitDistances.EuclideanIdentity
