import PlanarUnitDistances.ArchShift

namespace PlanarUnitDistances.Competition.GridRounding
open MeasureTheory Set Real Finset
open scoped Classical
noncomputable section

private lemma exp_hyp : Integrable (fun x : ℝ => exp (-|x|)) ∧ ∫x : ℝ,exp (-|x|)=2 := by
  have a : EqOn (fun x : ℝ => exp (-|x|)) exp (Iic 0) :=
    fun x hx => by change exp (-|x|)=exp x; rw [abs_of_nonpos (show x≤0 from hx),neg_neg]
  have b : EqOn (fun x : ℝ => exp (-|x|)) (fun x => exp (-x)) (Ioi 0) :=
    fun x hx => by change exp (-|x|)=exp (-x); rw [abs_of_pos (show 0<x from hx)]
  have ai := (integrableOn_exp_Iic 0).congr_fun a.symm measurableSet_Iic
  have bi := (integrableOn_exp_neg_Ioi 0).congr_fun b.symm measurableSet_Ioi
  have u := ai.union bi
  rw [Iic_union_Ioi,integrableOn_univ] at u
  refine ⟨u,?_⟩
  rw [←intervalIntegral.integral_Iic_add_Ioi ai bi,setIntegral_congr_fun measurableSet_Iic a,
    setIntegral_congr_fun measurableSet_Ioi b,integral_exp_Iic_zero,integral_exp_neg_Ioi_zero]
  norm_num

private lemma joint_integrable (n l h : ℝ) (z z' w w' : ℂ) :
    Integrable (fun x : ℝ×ℝ => failure n z z' w w' x.1 x.2) ((volume.restrict (Icc l h)).prod shift) := by
  apply Integrable.of_bound (failure_measurable ..).aestronglyMeasurable 1
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (failure_bounds ..).1]; exact (failure_bounds ..).2

theorem single_edge_average {n : ℝ} {z z' w w' : ℂ} (hz : ‖z-z'‖=exp (-n)) (hw : ‖w-w'‖=exp n) (l h : ℝ) :
    (∫u,∫s in Icc l h,failure n z z' w w' s u ∂volume ∂shift) ≤ 2*sqrt 2 := by
  let f := failure n z z' w w'
  have i := joint_integrable n l h z z' w w'
  have e1 : Integrable (fun s : ℝ => sqrt 2*exp (-|s-n|)) :=
    ((exp_hyp.1.comp_sub_right n).const_mul (sqrt 2))
  have e2 : (∫s : ℝ,sqrt 2*exp (-|s-n|))=2*sqrt 2 := by
    rw [integral_const_mul,integral_sub_right_eq_self (fun x : ℝ => exp (-|x|)) n,exp_hyp.2,mul_comm]
  have mono := integral_mono i.integral_prod_left e1.integrableOn (fun s => expected_failure hz hw s)
  rw [←integral_integral_swap i]
  exact mono.trans ((integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall (fun s => mul_nonneg (sqrt_nonneg _) (exp_pos _).le)) e1).trans_eq e2)

/-- One shift, chosen before sampling any edge, handles every edge of the
finite weighted graph throughout the prescribed interval of levels. -/
theorem one_shift {E : Type*} [Fintype E] (p : E → ℝ) (hp : ∀e,0≤p e) (total : ∑e,p e=1)
    (n : E → ℝ) (z z' w w' : E → ℂ) (hz : ∀e,‖z e-z' e‖=exp (-(n e)))
    (hw : ∀e,‖w e-w' e‖=exp (n e)) (l h : ℝ) :
    ∃u∈Ioo (0:ℝ) 1,(∑e,p e*(∫s in Icc l h,failure (n e) (z e) (z' e) (w e) (w' e) s u))≤2*sqrt 2 := by
  let J (e : E) (u : ℝ) := ∫s in Icc l h,failure (n e) (z e) (z' e) (w e) (w' e) s u
  have jI (e : E) : Integrable (J e) shift := (joint_integrable ..).integral_prod_right
  let F (u : ℝ) := ∑e,p e*J e u
  have fI : Integrable F shift := integrable_finsetSum _ (fun e _ => (jI e).const_mul _)
  have mean : (∫u,F u ∂shift)≤2*sqrt 2 := by
    unfold F
    rw [integral_finsetSum _ (fun e _ => (jI e).const_mul _)]
    simp_rw [integral_const_mul]
    apply (sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (single_edge_average (hz e) (hw e) l h) (hp e))).trans_eq
    rw [←Finset.sum_mul,total,one_mul]
  have inside : ∀ᵐu ∂shift,u∈Ioo (0:ℝ) 1 := by
    have h1 : ∀ᵐu ∂shift,u∈Ioc (0:ℝ) 1 := ae_restrict_mem measurableSet_Ioc
    have h2 : ∀ᵐu ∂shift,u≠1 := ae_restrict_of_ae (volume.ae_ne (1:ℝ))
    filter_upwards [h1,h2] with u hu ne
    exact ⟨hu.1,lt_of_le_of_ne hu.2 ne⟩
  have pos := measure_le_integral_pos fI
  by_contra! no
  have ae : ∀ᵐu ∂shift,¬F u≤∫v,F v ∂shift :=
    inside.mono fun u hu => not_le_of_gt (mean.trans_lt (no u hu))
  have zero := ae_iff.mp ae
  exact (ne_of_gt pos) (by simpa only [not_not] using zero)

end
end PlanarUnitDistances.Competition.GridRounding
