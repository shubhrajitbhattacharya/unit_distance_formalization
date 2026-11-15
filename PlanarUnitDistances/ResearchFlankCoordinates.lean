import PlanarUnitDistances.PhysicalScores
import PlanarUnitDistances.ShiftConsistency
import PlanarUnitDistances.FlankCharge

namespace PlanarUnitDistances.ResearchPhysical
open Competition Competition.IncidencePiece Real NumberField OAI.PlanarUnitDistances.BudgetPlaces
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

def flankConstant : Place K → ℝ := Sum.elim (fun _ => log 2) (fun _ => 0)

private theorem grid_norm (v : InfinitePlace K) (z : Competition.Plane → K) (u : ℝ×ℝ)
    (s : ℝ) (p q : Competition.Plane) (h : grid v z u s p=grid v z u s q) :
    v (z p-z q) ≤ exp (s+log 2) := by
  have hb := OAI.PlanarUnitDistances.StateConsistency.norm_le_sqrt_two_of_same_grid (exp_pos s)
    (z:=v.embedding (z p)) (w:=v.embedding (z q)) (u:=u) h
  rw [←map_sub,v.norm_embedding_eq] at hb
  rw [exp_add,exp_log (by norm_num : (0:ℝ)<2),mul_comm]
  have h2 : sqrt 2≤2 := by nlinarith [sq_sqrt (by norm_num : (0:ℝ)≤2)]
  exact hb.trans (mul_le_mul_of_nonneg_right h2 (exp_pos _).le)

/-- Physical equality in either stored coordinate gives the metric bounds
used for the two flanks, for the original shift and at this exact level. -/
theorem coordinate_matches (M : IncidencePiece K) (u : InfinitePlace K→ℝ) (v : Place K) (s : ℝ)
    (q r : Competition.Plane) (hq : q∈M.P∪M.Q) (hr : r∈M.P∪M.Q) :
    let t := M.recordsAt u v s
    ((t.label q).1=(t.label r).1 → valuation v (M.Z q-M.Z r)≤exp (-s+flankConstant v)) ∧
    ((t.label q).2=(t.label r).2 → valuation v (M.W q-M.W r)≤exp (s+flankConstant v)) := by
  cases v with
  | inl v =>
    have spec := M.arch_matches v (u v,u v) (u v,u v) s q r hq hr
    exact ⟨fun h => grid_norm v M.Z _ _ q r (spec.1.mp h),
      fun h => grid_norm v M.W _ _ q r (spec.2.mp h)⟩
  | inr v =>
    have spec := M.finite_matches v s q r hq hr
    constructor
    · intro h
      change v (M.Z q-M.Z r)≤exp (-s+0)
      rw [add_zero]; exact spec.1.mp h
    · intro h
      change v (M.W q-M.W r)≤exp (s+0)
      rw [add_zero]; exact spec.2.mp h

def jump (M : IncidencePiece K) (p q : Competition.Plane) := M.Z p-M.Z q

theorem jump_ne (M : IncidencePiece K) {p q : Competition.Plane} (he : (p,q)∈M.E) : jump M p q≠0 :=
  left_ne_zero_of_mul_eq_one (unit_model M he)

theorem jump_inverse (M : IncidencePiece K) {p q : Competition.Plane} (he : (p,q)∈M.E) :
    (jump M p q)⁻¹ = M.W p-M.W q := inv_eq_of_mul_eq_one_right (unit_model M he)

theorem distinct_jumps (M : IncidencePiece K) {p q r : Competition.Plane} (hq : (p,q)∈M.E)
    (hr : (p,r)∈M.E) (hqr : q≠r) : jump M p q ≠ jump M p r := by
  intro h
  apply hqr
  have eq : M.Z q=M.Z r := by unfold jump at h; exact sub_right_inj.mp h
  have a := (M.coordinates q (Finset.mem_union_right _ (Finset.mem_product.mp (M.membership hq)).2)).1
  have b := (M.coordinates r (Finset.mem_union_right _ (Finset.mem_product.mp (M.membership hr)).2)).1
  have z := a.symm.trans ((congrArg M.embedding eq).trans b)
  ext i
  fin_cases i
  · exact congrArg Complex.re z
  · exact congrArg Complex.im z

end
end PlanarUnitDistances.ResearchPhysical
