/- Adapted from OpenAI math, UnitDistances/HeightTransfer.lean and States.lean,
   adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0).
   The Euclidean square constants here are √2 in both geometric estimates. -/
import PlanarUnitDistances.HeightMesh

namespace OAI
namespace PlanarUnitDistances.GridShift
open MeasureTheory Set
noncomputable section

end
end PlanarUnitDistances.GridShift

namespace PlanarUnitDistances.StateConsistency
open MeasureTheory Set Real
open PlanarUnitDistances.GridShift
noncomputable section


lemma norm_le_sqrt_two_of_same_grid {r : ℝ} (hr : 0 < r)
    {z w : ℂ} {u : ℝ × ℝ} (h : gridLabel r z u = gridLabel r w u) :
    ‖z-w‖ ≤ Real.sqrt 2*r := by
  have hx := abs_sub_lt_one_of_floor_eq (congrArg Prod.fst h)
  have hy := abs_sub_lt_one_of_floor_eq (congrArg Prod.snd h)
  rw [add_sub_add_right_eq_sub,← sub_div,abs_div,abs_of_pos hr,div_lt_one hr] at hx hy
  have hx₂ : (z.re-w.re)^2 ≤ r^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (z.re-w.re)) hr.le).mpr hx.le
  have hy₂ : (z.im-w.im)^2 ≤ r^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (z.im-w.im)) hr.le).mpr hy.le
  have hn := Complex.sq_norm (z-w)
  rw [Complex.normSq_apply,Complex.sub_re,Complex.sub_im] at hn
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hb : 0 ≤ Real.sqrt 2*r := mul_nonneg (Real.sqrt_nonneg _) hr.le
  nlinarith [norm_nonneg (z-w)]


variable {E : Type*} [Fintype E]


def localSetoid {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (s : ℝ) : Setoid K :=
  { r := fun x y => v (x-y) ≤ exp s
    iseqv := ⟨by intro x; simpa using (exp_pos s).le,
      by intro x y h; rwa [v.map_sub],
      by
        intro x y z h₁ h₂
        have he : x-z = (x-y)+(y-z) := by ring
        rw [he]; exact (hv _ _).trans (max_le h₁ h₂)⟩ }


open scoped Classical


end
end PlanarUnitDistances.StateConsistency

end OAI
