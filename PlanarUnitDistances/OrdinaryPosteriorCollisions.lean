import PlanarUnitDistances.FullHistoryLists
import PlanarUnitDistances.UniformIncidenceLaw

namespace PlanarUnitDistances.ComparisonConstants
open Real Filter Finset OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open FiniteLaw FiniteStarCoupling UniformPhysical
open scoped Topology Classical
noncomputable section

/-- All size parameters behind ordinary posterior collisions, uniformly
in the number field and in the particular configuration. -/
theorem eventual_ordinary_degrees :
    ∀ᶠt : ℝ in atTop, t^(-150*(3*exactGap))≤dy 144000 ∧
      ∀(P Q : Finset Plane) (M : CommonFieldModel.Model P Q), ProofAssembly.LargePiece t P Q M →
      (∀p∈P,(2:ℝ)^144000≤degree Q p) ∧ (∀q∈Q,(2:ℝ)^144000≤degree P q) := by
  let g := 3*exactGap
  have gp : 0<g := by dsimp [g]; positivity [exactGap_pos]
  have hl := exactGap_lt_largeHeightGap.trans_le (Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1:ℝ)≤2) (by norm_num : -(594036:ℝ)≤ -32))
  have ppos : 0<1-90*g := by dsimp [g]; norm_num [Real.rpow_neg] at hl; linarith
  have qpos : 0<10000*g-90*g := by linarith only [gp]
  have small := (tendsto_rpow_neg_atTop (show 0<150*g by positivity)).eventually
    (eventually_le_nhds (pos 144000))
  have pbig := (tendsto_rpow_atTop ppos).eventually_ge_atTop ((100/27:ℝ)*(2:ℝ)^144000)
  have qbig := (tendsto_rpow_atTop qpos).eventually_ge_atTop ((50/27:ℝ)*(2:ℝ)^144000)
  filter_upwards [small,pbig,qbig] with t hx hp hq
  refine ⟨by simpa only [neg_mul,g] using hx,?_⟩
  intro P Q M piece
  obtain ⟨_,_,_,_,_,degP,_,degQ,_,_,_⟩ := piece
  constructor
  · intro p mem
    have bound := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤27/100)
    rw [←mul_assoc,show (27/100:ℝ)*(100/27)=1 by norm_num,one_mul] at bound
    exact bound.trans (degP p mem).1
  · intro q mem
    have bound := mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ)≤27/50)
    rw [←mul_assoc,show (27/50:ℝ)*(50/27)=1 by norm_num,one_mul] at bound
    exact bound.trans (degQ q mem).1

private lemma diagonal_le_max {A : Type*} [Fintype A] (μ : Law A) {a : ℝ}
    (m : ∀x,μ.val x≤a) : ∑x,(μ.val x)^2≤a := by
  calc
    _ ≤ ∑x,a*μ.val x := sum_le_sum (fun x _ => by rw [pow_two]; exact mul_le_mul_of_nonneg_right (m x) (μ.nonneg x))
    _ = a := by rw [←mul_sum,μ.total,mul_one]

/-- Both posterior diagonal probabilities on the actual uniform unit
graph are bounded at every chosen base, even before averaging the bases. -/
theorem eventual_ordinary_collisions :
    ∀ᶠt : ℝ in atTop, ∀(P Q : Finset Plane) (M : CommonFieldModel.Model P Q),
    ProofAssembly.LargePiece t P Q M → ∀(he : 0 < incidences P Q),
    let G := edgeLaw (unitRows P Q) (incidences P Q) he (unitRows_total P Q)
    (∀p : P,∑q,((row G p).val q)^2≤dy 144000) ∧
    (∀q : Q,∑p,((col G q).val p)^2≤dy 144000) := by
  filter_upwards [eventual_ordinary_degrees] with t ht
  intro P Q M piece he
  obtain ⟨dp,dq⟩ := ht.2 P Q M piece
  let G := edgeLaw (unitRows P Q) (incidences P Q) he (unitRows_total P Q)
  dsimp only
  have cap {d : ℝ} (hd : (2:ℝ)^144000≤d) : d⁻¹≤dy 144000 := inv_anti₀ (by positivity) hd
  constructor
  · intro p
    apply diagonal_le_max
    intro q
    have hp : 0<degree Q p := (pow_pos (by norm_num : (0:ℝ)<2) _).trans_le (dp p p.prop)
    have e : (left G).val p=degree Q p/incidences P Q := by rw [edge_left,unitRows_point_degree]
    change (row G p).val q≤_
    rw [row_val G (e.symm ▸ div_pos hp he) q,e]
    apply le_trans _ (cap (dp p p.prop))
    change UniformNormalization.weight (unitRows P Q) (incidences P Q) p q / _≤_
    unfold UniformNormalization.weight
    by_cases h : p∈unitRows P Q q
    · rw [ite_eq_left h]; exact le_of_eq (by field_simp)
    · rw [ite_eq_right h,zero_div]; positivity
  · intro q
    apply diagonal_le_max
    intro p
    have hq : 0<degree P q := (pow_pos (by norm_num : (0:ℝ)<2) _).trans_le (dq q q.prop)
    have e : (right G).val q=degree P q/incidences P Q := by rw [edge_right,BoundedHeight.centerLaw,unitRows_center_degree]
    change (col G q).val p≤_
    rw [col_val G (e.symm ▸ div_pos hq he) p,e]
    apply le_trans _ (cap (dq q q.prop))
    change UniformNormalization.weight (unitRows P Q) (incidences P Q) p q / _≤_
    unfold UniformNormalization.weight
    by_cases h : p∈unitRows P Q q
    · rw [ite_eq_left h]; exact le_of_eq (by field_simp)
    · rw [ite_eq_right h,zero_div]; positivity

end
end PlanarUnitDistances.ComparisonConstants

