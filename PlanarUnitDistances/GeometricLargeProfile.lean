import PlanarUnitDistances.IncidencePiece
import PlanarUnitDistances.CommonCoordinates
import PlanarUnitDistances.GeometricHeightLaw
import PlanarUnitDistances.LargeProfile

namespace PlanarUnitDistances
open Filter OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open UniformNormalization EdgeHeightScale
open scoped Topology
noncomputable section

/-- The interval contains every edge threshold as well as both endpoint
quantities needed for distinct point pairs in the later two-coordinate comparison. -/
def profileRadius {P Q : Type} [Fintype P] [Fintype Q] {K : Type*} [Field K]
    (S : Q → Finset P) (Z W : P ⊕ Q → K) (v : AbsoluteValue K ℝ) :=
  (∑ x : P × Q, |-Real.log (v (direction S Z x))|) +
  (∑ x : P × P, (|Real.log (v (Z (.inl x.1)-Z (.inl x.2)))| +
    |Real.log (v (W (.inl x.1)-W (.inl x.2)))|))

theorem radius_bounds {P Q : Type} [Fintype P] [Fintype Q] {K : Type*} [Field K]
    (S : Q → Finset P) (Z W : P ⊕ Q → K) (v : AbsoluteValue K ℝ) :
    (∀ x, |threshold v (direction S Z) x| ≤ profileRadius S Z W v) ∧
    (∀ p r, |Real.log (v (Z (.inl p)-Z (.inl r)))| ≤ profileRadius S Z W v ∧
      |Real.log (v (W (.inl p)-W (.inl r)))| ≤ profileRadius S Z W v) := by
  unfold profileRadius
  constructor
  · intro x
    exact (Finset.single_le_sum (fun y _ => abs_nonneg (-Real.log (v (direction S Z y)))) (Finset.mem_univ x)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)))
  · intro p r
    let f (x : P × P) := |Real.log (v (Z (.inl x.1)-Z (.inl x.2)))|+
      |Real.log (v (W (.inl x.1)-W (.inl x.2)))|
    have hf (y : P × P) (_ : y ∈ Finset.univ) : 0 ≤ f y := add_nonneg (abs_nonneg _) (abs_nonneg _)
    have h := Finset.single_le_sum hf (Finset.mem_univ (p,r))
    have hpos := Finset.sum_nonneg (s := Finset.univ) (fun (y : P × Q) _ => abs_nonneg (-Real.log (v (direction S Z y))))
    dsimp [f] at h
    constructor <;> linarith [abs_nonneg (Real.log (v (W (.inl p)-W (.inl r)))),
      abs_nonneg (Real.log (v (Z (.inl p)-Z (.inl r))))]

/-- With finitely many directions and point differences only finitely many finite
primes require nondegenerate level intervals. This includes zero coordinates. -/
theorem radius_finite_support {P Q : Type} [Fintype P] [Fintype Q] {K : Type*}
    [Field K] [NumberField K] (S : Q → Finset P) (Z W : P ⊕ Q → K) :
    Function.HasFiniteSupport (fun v : NumberField.FinitePlace K => profileRadius S Z W v.val) := by
  have logSupport (x : K) :
      Function.HasFiniteSupport (fun v : NumberField.FinitePlace K => |Real.log (v x)|) := by
    by_cases h : x = 0
    · subst x
      simp [Function.HasFiniteSupport,Function.support]
    · apply (NumberField.FinitePlace.hasFiniteMulSupport h).subset
      intro v hv
      change v x ≠ 1
      intro one
      exact hv (by simp [one])
  unfold profileRadius
  simp only [abs_neg,← NumberField.FinitePlace.coe_apply]
  apply Function.HasFiniteSupport.fun_add
  · exact Function.HasFiniteSupport.sum (fun x => logSupport (direction S Z x)) Finset.univ
  · exact Function.HasFiniteSupport.sum (fun x : P × P => Function.HasFiniteSupport.fun_add
      (logSupport (Z (.inl x.1)-Z (.inl x.2))) (logSupport (W (.inl x.1)-W (.inl x.2)))) Finset.univ

/-- The real-plane dense input at the stated exponent yields actual original
unit directions with minority integral greater than 2^2100. The same two
sets retain the crucial size, edge, expansion and information conclusions. -/
theorem dense_large_profile :
    let g := 3*exactGap
    let a := 10000*g
    ∀ᶠ t : ℝ in atTop, ∀ X : Finset Plane, (X.card:ℝ)=t^3 →
      t^(4-g) ≤ ((orderedPairs X).card:ℝ) →
      ∃ (P Q : Finset Plane) (M : CommonFieldModel.Model P Q),
        (∀ p ∈ P, ∀ i, IsAlgebraic ℚ (p i)) ∧
        t^(1+2*a-173*g) ≤ (P.card:ℝ) ∧ (P.card:ℝ) ≤ 2*t^(1+2*a) ∧
        (Q.card:ℝ) ≤ t^(2+a) ∧ t^(2+2*a-90*g) ≤ incidences P Q ∧
        (∀ p ∈ P, (27/100:ℝ)*t^(1-90*g) ≤ degree Q p ∧ degree Q p ≤ t^(1+10*g) ∧
          (27/50:ℝ)/P.card ≤ degree Q p/incidences P Q ∧
          degree Q p/incidences P Q ≤ t^(-1-2*a+100*g)) ∧
        t^(-1-2*a+100*g) ≤ t^(-1:ℝ) ∧
        (∀ q ∈ Q, (27/50:ℝ)*t^(a-90*g) ≤ degree P q ∧ degree P q ≤ t^(a+10*g) ∧
          (27/50:ℝ)/Q.card ≤ degree P q/incidences P Q) ∧
        (∀ A ⊆ P, ∀ B ⊆ Q, let z := (A.card:ℝ)/P.card*((B.card:ℝ)/Q.card)
          incidences A B/incidences P Q ≤ Real.sqrt z*(z^(1/25:ℝ)+t^(-150*g))) ∧
        unitWalkInformation P Q+1 ≤ 10200*g*Real.log t ∧
        let r := profileRadius (unitRows P Q) M.z M.w
        (2:ℝ)^2100 < profileScale (unitRows P Q) (incidences P Q) M.z (fun v => -r v) r := by
  dsimp only
  let g := 3*exactGap
  let a := 10000*g
  have hg : 0 < g := mul_pos (by norm_num) exactGap_pos
  have hgsmall : a ≤ 1/10 := by
    have hb := exactGap_lt_largeHeightGap.trans_le
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (by norm_num : (-(594036:ℝ)) ≤ -(32:ℝ)))
    rw [Real.rpow_neg (by norm_num),← Nat.cast_ofNat (R := ℝ) (n:=32),Real.rpow_natCast] at hb
    norm_num1 at hb
    dsimp [a,g]
    linarith
  have hdeg : 0 < 1-90*g := by dsimp [a] at hgsmall; linarith
  have hlev := (tendsto_rpow_neg_atTop (by linarith : 0 < 150*g)).eventually
    (eventually_le_nhds (by positivity : (0:ℝ) < 1/2^100))
  have hcol := (tendsto_rpow_neg_atTop (by linarith : 0 < 19900*g)).eventually
    (eventually_le_nhds (by norm_num : (0:ℝ) < 1/100))
  filter_upwards [algebraic_incidence_piece hg hgsmall, eventually_gt_atTop (0:ℝ),hlev,hcol,
    (tendsto_rpow_atTop hdeg).eventually_ge_atTop (300/(27/100):ℝ)] with t piece ht hlev hcol dlarge
  intro X hc hdense
  obtain ⟨P,Q,hPAlg,hQAlg,mlo,mhi,qhi,edge,degP,thetaSmall,degQ,cut,info⟩ := piece X hc hdense
  obtain ⟨M⟩ := CommonFieldModel.exists_model hPAlg hQAlg
  refine ⟨P,Q,M,hPAlg,mlo,mhi,qhi,edge,degP,thetaSmall,degQ,cut,info,?_⟩
  have ep := (Real.rpow_pos_of_pos ht _).trans_le edge
  have mp := (Real.rpow_pos_of_pos ht _).trans_le mlo
  have qp := pos_of_mul_pos_right (ep.trans_le (incidences_le P Q)) (Nat.cast_nonneg _)
  have rowpos (q : Plane) (hq : q∈Q) : 0 < degree P q :=
    lt_of_lt_of_le (mul_pos (by norm_num) (Real.rpow_pos_of_pos ht _)) (degQ q hq).1
  have nonemp (q : Q) : (unitRows P Q q).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp
    (by rw [unitRows_center_degree]; exact rowpos q q.prop : (0:ℝ) < (unitRows P Q q).card))
  let r := profileRadius (unitRows P Q) M.z M.w
  have ctrl := unitRows_label_control P Q mp qp ep (Real.rpow_nonneg ht.le (-150*g))
    (by simpa only [neg_mul] using hlev) (fun p hp => (degP p hp).2.2.1)
    (fun q hq => (degQ q hq).2.2) cut
  apply scale_large (unitRows P Q) nonemp ep (unitRows_total P Q) ctrl M.z M.w
    M.point_injective M.center_injective (fun q p hp => M.unit_identity p q (Finset.mem_filter.mp hp).2)
    (fun v => -r v) r
    (fun v x => (abs_le.mp ((radius_bounds _ M.z M.w v).1 x)).1)
    (fun v x => (abs_le.mp ((radius_bounds _ M.z M.w v).1 x)).2)
    (θ := t^(-1-2*a+100*g)) (t := t) (Real.rpow_nonneg ht.le _) ht
  · calc
      _ = t^(1+(-1-2*a+100*g)) := by rw [Real.rpow_add ht 1 (-1-2*a+100*g),Real.rpow_one]
      _ = t^(-(19900*g)) := by congr 1; dsimp [a]; ring
      _ ≤ _ := hcol
  · intro p
    rw [unitRows_point_degree]
    exact (degP p p.prop).2.2.2
  · intro p
    rw [unitRows_point_degree]
    exact le_trans (by linarith : (300:ℝ) ≤ 27/100*t^(1-90*g)) (degP p p.prop).1
  · rw [← unitRows_information P Q rowpos]
    simpa only [g,show ∀ x : ℝ, 10200*(3*x)=30600*x by intro; ring] using info

end
end PlanarUnitDistances
