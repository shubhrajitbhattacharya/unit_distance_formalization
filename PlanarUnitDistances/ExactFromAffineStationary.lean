import PlanarUnitDistances.ResearchMotion
import PlanarUnitDistances.LargeScaleCounting
import PlanarUnitDistances.UniformGridSeparator
import PlanarUnitDistances.Main
import PlanarUnitDistances.GridLocus
import PlanarUnitDistances.MovingGridAnchors
import PlanarUnitDistances.EffectiveGridGeometry
import PlanarUnitDistances.TripleSelection

namespace PlanarUnitDistances
open Filter Finset
open scoped Topology
noncomputable section

theorem eventual_graph_bound_of_scale_motion {minScale : ℝ}
    (motionAt : ∀ (n : ℕ) (K : Type) [Field K] [NumberField K] (G : AdmissibleGraph n K),
      minScale ≤ G.scale → MovingGrid.Motion G)
    (uniform : GridLocus.UniformExceptionalDegree) : EventualAlgebraicGraphBoundAtScale minScale := by
  obtain ⟨E, eff⟩ := uniform
  have grows : Tendsto (fun n : ℕ => (n:ℝ)^(3/5:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 3/5)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2^10000 : ℕ), grows.eventually_gt_atTop
    (12*CurveRestriction.curveDegree*(E:ℝ)*CurveRestriction.restrictionCost^32)]
    with n hn growth
  intro K _ _ G hscale
  by_contra! dense
  have motion : MovingGrid.Motion G := by
    exact motionAt n K G hscale
  obtain ⟨R⟩ := GraphRestriction.retain G hn dense (MovingGrid.curvesForRows motion)
  have an := (card_le_card R.left_subset).trans G.point_bound
  have bn := (card_le_card R.right_subset).trans G.point_bound
  have hn0 : 0 < n := (pow_pos (by decide : 0 < 2) _).trans_le hn
  exact GridLocus.excludes_dense_real_graph_of_degree E eff R.f R.g R.curve_pair R.left.degree R.right.degree
    R.A R.B (card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) R.left.many))
    (card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) R.right.many))
    R.left.vanishes R.right.vanishes G.edges n (by exact_mod_cast hn0) growth an bn R.dense
    (MovingGrid.compatible motion)

namespace ResearchPhysical

/-- The bound only uses the full normalized multiplier ideals, at the
large scale retained by the original common-center extraction. -/
theorem exact_from_affine_stationary_heights {A D : ℝ}
    (hA : A ≤ (2:ℝ)^2086) (hD : D ≤ (2:ℝ)^113)
    (heights : ResearchMotion.LocalizedGridWithCap (fun s => A+D*s)) : TheoremA := by
  let cap : ℝ → ℝ := fun s => (2:ℝ)^2086 + (2:ℝ)^113*s
  have mono : Monotone cap := fun s t h => add_le_add (le_refl _) (mul_le_mul_of_nonneg_left h (by positivity))
  have heightMax : ResearchMotion.LocalizedGridWithCap cap := by
    intro K _ _ _ I J _ _ r a i j row col mi ma lj hj hr pick c P hP hc hq
    have hh := heights K I J r a i j row col mi ma lj hj hr pick c P hP hc hq
    exact hh.trans (add_le_add hA (mul_le_mul_of_nonneg_right hD (Finset.sum_nonneg fun _ _ => weilHeight_nonneg _)))
  apply theoremA_of_eventual_large_scale_graph
  apply eventual_graph_bound_of_scale_motion _ GridLocus.uniform_exceptional_degree
  intro n K _ _ G floor
  apply ResearchMotion.motion_with_cap cap mono heightMax G
  intro h low high
  have small : (2:ℝ)^2086 ≤ G.scale*(125/4096) := by
    have eq : (2:ℝ)^2086 = ((2:ℝ)^2100/500)*(125/4096) := by
      rw [show (2100:ℕ) = 2086+14 by decide, pow_add]
      ring
    exact eq.le.trans (mul_le_mul_of_nonneg_right floor (by norm_num))
  have slope : (2:ℝ)^113 * (24*(G.scale/(324*2^111))) = (8/27)*G.scale := by ring
  change h ≤ (2:ℝ)^2086 + (2:ℝ)^113*(24*(G.scale/(324*2^111))) at high
  rw [slope] at high
  have pos : 0 < G.scale := (by norm_num : (0:ℝ) < (2:ℝ)^2100/500).trans_le floor
  have contradict (a S y : ℝ) (hS : 0<S) (ha : a ≤ S*(125/4096))
      (hl : S/3 ≤ y) (hu : y ≤ a+(8/27)*S) : False := by linarith only [hS,ha,hl,hu]
  exact contradict _ _ _ pos small low high

end ResearchPhysical
end
end PlanarUnitDistances
