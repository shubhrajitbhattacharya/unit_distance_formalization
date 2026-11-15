import PlanarUnitDistances.TripleSelection
import PlanarUnitDistances.CollisionAbsorption
import PlanarUnitDistances.WeightedHistoryLists
import PlanarUnitDistances.OrdinaryPosteriorCollisions

namespace PlanarUnitDistances.ComparisonConstants
open Real Filter Finset OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open FiniteLaw FiniteStarCoupling TemplateCoupling UniformPhysical
open scoped Topology Classical
noncomputable section

private lemma absorb_collision {S W X : ℝ} (hS : (2:ℝ)^2100<S)
    (hW : W≤S/dy 1800) (hX : X≤4*S) :
    2*log 2+dy 144000*(2*(W+X)) ≤ dy 144*S := by
  rw [mul_comm (dy 144000)]
  exact collision_absorption hS hW hX (pos 144000).le le_rfl

private lemma ordinary_error {A : Type*} [Fintype A] (μ : Law A) (H m : A→ℝ)
    {S W : ℝ} (hS : (2:ℝ)^2100<S) (w : 0≤W) (hw : W≤S/dy 1800)
    (hp : ∀x,0≤H x) (hmean : avg μ H≤4*S) (hcap : ∀x,m x≤dy 144000) :
    2*log 2+avg μ (fun x => 2*(W+H x)*m x)≤dy 144*S := by
  have est : avg μ (fun x => 2*(W+H x)*m x) ≤ avg μ (fun x => dy 144000*(2*(W+H x))) :=
    avg_mono μ (fun x => (mul_le_mul_of_nonneg_left (hcap x) (mul_nonneg (by norm_num) (add_nonneg w (hp x)))).trans_eq (mul_comm ..))
  rw [avg_smul,avg_smul,avg_add,avg_const] at est
  exact (add_le_add (le_refl _) est).trans (absorb_collision hS hw hmean)


private theorem weighted_channel_collision :
    ∀ {t : ℝ}, 0 < t → ∀ (P Q : Finset Plane) (M : CommonFieldModel.Model P Q),
      ProofAssembly.LargePiece t P Q M → ∀ (he : 0 < incidences P Q) {T : Type*} [Fintype T] (a : Q → Law T),
      (∀ p ∈ P, (Fintype.card T:ℝ)/degree Q p ≤ dy 144000) →
      ∀ (H : P → ℝ), (∀p,0≤H p) →
      let G := edgeLaw (unitRows P Q) (incidences P Q) he (unitRows_total P Q)
      (∑p,H p*(∑j,(templates G a).val j*(left (slice G a j)).val p*
        ∑q,((row (slice G a j) p).val q)^2)) ≤ dy 144000 * avg (left G) H := by
  intro t ht P Q M piece he T _ a cap H hH
  let G := edgeLaw (unitRows P Q) (incidences P Q) he (unitRows_total P Q)
  have deg := piece.2.2.2.2.2.1
  change (∑p,H p*(∑j,(templates G a).val j*(left (slice G a j)).val p*
        ∑q,((row (slice G a j) p).val q)^2)) ≤ dy 144000 * avg (left G) H
  unfold avg
  rw [mul_sum]
  apply sum_le_sum
  intro p _
  have dp : 0<degree Q p := (mul_pos (by norm_num) (Real.rpow_pos_of_pos ht _)).trans_le (deg p p.prop).1
  have acc := slice_collision_at G a p (posterior_row_cap he p dp)
  have boot := mul_le_mul_of_nonneg_left acc (hH p)
  have limit := mul_le_mul_of_nonneg_right (cap p p.prop) (mul_nonneg ((left G).nonneg p) (hH p))
  apply boot.trans
  simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using limit

/-- All three diagonal costs for an arbitrary finite template alphabet. The single
cardinality-per-degree bound can be applied before specializing any history type. -/
theorem collision_errors_of_cardinal :
    ∀ᶠt : ℝ in atTop, ∀(P Q : Finset Plane) (M : CommonFieldModel.Model P Q),
    ProofAssembly.LargePiece t P Q M → ∀(he : 0 < incidences P Q) {T : Type*} [Fintype T] (a : Q→Law T),
      (∀ p ∈ P, (Fintype.card T:ℝ)/degree Q p ≤ dy 144000) → ∀ (X : P→ℝ) (Y : Q→ℝ) (W : ℝ),
      let S := ProofAssembly.pieceScale M
      let G := edgeLaw (unitRows P Q) (incidences P Q) he (unitRows_total P Q)
      0≤W → W≤S/dy 1800 → (∀p,0≤X p) → (∀q,0≤Y q) → avg (left G) X≤4*S → avg (right G) Y≤4*S →
      (2*log 2+avg (right G) (fun q => 2*(W+Y q)*(∑p,((col G q).val p)^2))≤dy 144*S) ∧
      (2*log 2+avg (left G) (fun p => 2*(W+X p)*(∑q,((row G p).val q)^2))≤dy 144*S) ∧
      (2*log 2+∑p,2*(W+X p)*(∑j,(templates G a).val j*(left (slice G a j)).val p*
        ∑q,((row (slice G a j) p).val q)^2)≤dy 144*S) := by
  filter_upwards [eventual_ordinary_collisions,eventually_gt_atTop (0:ℝ)] with t ord ht
  intro P Q M piece he T _ a cap X Y W
  dsimp only
  intro w hw xp yp mx my
  let G := edgeLaw (unitRows P Q) (incidences P Q) he (unitRows_total P Q)
  have big : (2:ℝ)^2100 < ProofAssembly.pieceScale M := piece.2.2.2.2.2.2.2.2.2.2
  obtain ⟨rowcap,colcap⟩ := ord P Q M piece he
  refine ⟨ordinary_error (right G) Y _ big w hw yp my colcap,ordinary_error (left G) X _ big w hw xp mx rowcap,?_⟩
  have cost := weighted_channel_collision ht P Q M piece he a cap (fun p => 2*(W+X p)) (fun p => mul_nonneg (by norm_num) (add_nonneg w (xp p)))
  dsimp only at cost
  rw [avg_smul,avg_add,avg_const] at cost
  exact (add_le_add (le_refl _) cost).trans (absorb_collision big hw mx)

end
end PlanarUnitDistances.ComparisonConstants
