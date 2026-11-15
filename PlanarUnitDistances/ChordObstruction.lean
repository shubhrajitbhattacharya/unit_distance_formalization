import PlanarUnitDistances.QuadraticKummerInput

/-! The four roots in the row obstruction are the actual differences of
inverse edge labels and edge labels in the chord equations. -/
namespace PlanarUnitDistances.FourRowObstruction
open IntermediateField Set
noncomputable section

variable {K E : Type*} [Field K] [CharZero K] [Field E] [CharZero E] [Algebra K E]

omit [CharZero E] in
/-- A reciprocal pair satisfying the Euclidean chord equation gives a root
of the specified radicand with the sign supplied by the original labels. -/
theorem chord_root {u m l : E} (inv : u*m=1) (chord : l=2-u-m) :
    (m-u)^2=l*(l-4) := by
  rw [chord]
  linear_combination -4*inv


end
end PlanarUnitDistances.FourRowObstruction
