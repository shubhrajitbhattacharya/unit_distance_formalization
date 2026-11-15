import PlanarUnitDistances.ArithmeticLevels
import PlanarUnitDistances.ShiftBudget

namespace PlanarUnitDistances.Competition.IncidencePiece
open MeasureTheory NumberField Real Finset Set GridRounding
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

private lemma edge_average (M : IncidencePiece K) (A : Plane×Plane → Prop) :
    M.edgeProb A=∑e : M.E,(1/(M.E.card:ℝ))*(if A e.val then (1:ℝ) else 0) := by
  rw [sum_coe_sort M.E (fun e => (1/(M.E.card:ℝ))*(if A e then (1:ℝ) else 0)),←mul_sum,
    ←natCast_card_filter,edgeProb]
  ring

private lemma actual_failure (M : IncidencePiece K) (v : InfinitePlace K) (s u : ℝ) (e : Plane×Plane) (he : e∈M.E) :
    (if ¬(archRecord M v (u,u) (u,u) s).consistent e then (1:ℝ) else 0)=
      failure (M.threshold v e) (v.embedding (M.Z e.1)) (v.embedding (M.Z e.2))
        (v.embedding (M.W e.1)) (v.embedding (M.W e.2)) s u := by
  obtain ⟨hp,hq⟩ := mem_product.mp (M.membership he)
  obtain ⟨za,wa⟩ := arch_matches M v (u,u) (u,u) s _ _ (mem_union_left _ hp) (mem_union_right _ hq)
  unfold CoordinateLevel.consistent
  rw [arch_bit M v _ _ s e he]
  by_cases h : s<M.threshold v e <;>
    by_cases z : grid v M.Z (u,u) (-s) e.1=grid v M.Z (u,u) (-s) e.2 <;>
    by_cases w : grid v M.W (u,u) s e.1=grid v M.W (u,u) s e.2 <;>
    simp only [h,decide_true,decide_false,ite_true,ite_false,za,wa] <;>
    simp_all [grid,GridRounding.failure,square] <;> split_ifs <;> grind

private lemma arch_lengths (M : IncidencePiece K) (v : InfinitePlace K) (e : M.E) :
    ‖v.embedding (M.Z e.val.1)-v.embedding (M.Z e.val.2)‖=exp (-(M.threshold v e.val)) ∧
    ‖v.embedding (M.W e.val.1)-v.embedding (M.W e.val.2)‖=exp (M.threshold v e.val) := by
  let x := M.Z e.val.1-M.Z e.val.2
  let y := M.W e.val.1-M.W e.val.2
  have unit : v x*v y=1 := by rw [←map_mul,unit_model M e.prop,map_one]
  have pos : 0<v x := lt_of_le_of_ne (apply_nonneg v _) (by intro h; simp [←h] at unit)
  have inv : v y=(v x)⁻¹ := by field_simp; linarith only [unit]
  rw [←map_sub,←map_sub,v.norm_embedding_eq,v.norm_embedding_eq]
  change v x=exp (- -log (v x)) ∧ v y=exp (-log (v x))
  rw [neg_neg,exp_neg,exp_log pos]; exact ⟨rfl,inv⟩

/-- At each infinite place a single fractional shift shared by both axes
of both grids makes the incidence-averaged integral at most 2√2. -/
theorem arch_shift (M : IncidencePiece K) (he : 0<(M.E.card:ℝ)) (v : InfinitePlace K) (l h : ℝ) :
    ∃u∈Ioo (0:ℝ) 1,(∫s in Icc l h,M.inconsistentMass (archRecord M v (u,u) (u,u) s))≤2*sqrt 2 := by
  let z (e : M.E) := v.embedding (M.Z e.val.1)
  let z' (e : M.E) := v.embedding (M.Z e.val.2)
  let w (e : M.E) := v.embedding (M.W e.val.1)
  let w' (e : M.E) := v.embedding (M.W e.val.2)
  let n (e : M.E) := M.threshold v e.val
  let p (_ : M.E) := 1/(M.E.card:ℝ)
  have pp : 0≤1/(M.E.card:ℝ) := by positivity
  obtain ⟨u,hf,avg⟩ := one_shift p (fun _ => pp) (by simp [p,nsmul_eq_mul,div_eq_mul_inv,he.ne'])
    n z z' w w' (fun e => (arch_lengths M v e).1) (fun e => (arch_lengths M v e).2) l h
  refine ⟨u,hf,?_⟩
  let f := fun e s => failure (n e) (z e) (z' e) (w e) (w' e) s u
  have sum (s : ℝ) : M.inconsistentMass (archRecord M v (u,u) (u,u) s)=∑e,p e*f e s := by
    unfold inconsistentMass
    rw [edge_average]
    apply sum_congr rfl
    intro e _
    by_cases hc : (archRecord M v (u,u) (u,u) s).consistent e <;>
      simpa [hc,p,f,n,z,z',w,w'] using congrArg (p e*·) (actual_failure M v s u e e.prop)
  have intF (e : M.E) : Integrable (f e) (volume.restrict (Icc l h)) := by
    have m : Measurable (f e) := (failure_measurable ..).comp (measurable_id.prodMk measurable_const)
    apply Integrable.of_bound m.aestronglyMeasurable 1
    filter_upwards [] with s
    change ‖failure (n e) (z e) (z' e) (w e) (w' e) s u‖≤1
    rw [Real.norm_eq_abs,abs_of_nonneg (failure_bounds ..).1]
    exact (failure_bounds ..).2
  simp_rw [sum]
  rw [integral_finsetSum _ (fun e _ => (intF e).const_mul _)]
  simp_rw [integral_const_mul]
  exact avg


end
end PlanarUnitDistances.Competition.IncidencePiece
