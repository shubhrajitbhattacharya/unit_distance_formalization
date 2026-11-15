import PlanarUnitDistances.ExtractionAssembly
import PlanarUnitDistances.RichCircles

namespace PlanarUnitDistances
open Filter OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence Finset
open scoped Classical Topology
noncomputable section

private theorem restrict_sum {A : Type*} [Fintype A] [DecidableEq A] (s : Finset A) (f : A → ℝ) :
    (∑ x ∈ s,f x) = ∑ x,if x∈s then f x else 0 := by rw [←sum_filter]; simp
/-- Reindex the projected pair-fiber mass in center-first sampling order.
This holds for any event, including fibers containing nonincident endpoints. -/
theorem goodTripleMass_center_sum {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (S : J → Finset I) (H : I×I → Finset J) {e : ℝ} (he : 0 < e) :
    goodTripleMass S H e =
      ∑ q, ∑ p ∈ S q, ∑ r ∈ S q,
        if q ∈ H (p,r) then (e*((S q).card:ℝ))⁻¹ else 0 := by
  let w (z : I×I) (q : J) :=
    ((S q).card:ℝ)/e*(if z.1 ∈ S q then ((S q).card:ℝ)⁻¹ else 0)*
      (if z.2 ∈ S q then ((S q).card:ℝ)⁻¹ else 0)
  have allPairs : goodTripleMass S H e = ∑ z, ∑ q ∈ H z,w z q := by
    apply sum_subset (subset_univ _)
    intro z _ h
    have hn : ¬(H z).Nonempty := fun hn => h (mem_filter.mpr ⟨mem_univ _,hn⟩)
    simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  rw [allPairs]
  simp_rw [restrict_sum (H _), restrict_sum (S _)]
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro p _
  by_cases hp : p∈S q
  · rw [if_pos hp]
    apply sum_congr rfl
    intro r _
    by_cases hr : r∈S q <;> by_cases hz : q∈H (p,r) <;> simp [w,hp,hr,hz]
    have hd : (0:ℝ) < (S q).card := Nat.cast_pos.mpr (card_pos.mpr ⟨p,hp⟩)
    field_simp
  · rw [if_neg hp]
    simp [w,hp]

/-- The final admissibility condition for an ordered endpoint pair, quantified
over every real center, independently of the sampled center set. -/
def circleSafe (P : Finset Plane) (z : P×P) : Prop :=
  ∀ c : Plane,dist (z.1:Plane) c=1 → dist (z.2:Plane) c=1 →
    ((circlePoints P c).card:ℝ) < (P.card:ℝ)^(9/10:ℝ)

/-- Drop all centers for a forbidden endpoint pair, preserving the other fibers exactly. -/
def removeRichPairs {P Q : Finset Plane} (H : P×P → Finset Q) (z : P×P) : Finset Q :=
  if circleSafe P z then H z else ∅

theorem mem_removeRichPairs {P Q : Finset Plane} (H : P×P → Finset Q) (z : P×P) (q : Q) :
    q∈removeRichPairs H z ↔ q∈H z ∧ circleSafe P z := by
  by_cases h : circleSafe P z <;> simp [removeRichPairs,h]

private theorem sum_unitRows (P Q : Finset Plane) (q : Q) (f : Plane → ℝ) :
    (∑ p ∈ unitRows P Q q, f p) = ∑ p ∈ circlePoints P q,f p := by
  have h : (unitRows P Q q).map (Function.Embedding.subtype (·∈P)) = circlePoints P q := by
    ext p
    simp [unitRows,unitNeighbors,circlePoints,and_comm]
  rw [←h,sum_map]
  rfl

private def lossSum (P Q C : Finset Plane) :=
  ∑ q ∈ Q, ∑ p ∈ circlePoints P q,
    ∑ _r ∈ (circlePoints P q).filter (fun r => ∃ c∈C,dist p c=1 ∧ dist r c=1),
      (incidences P Q*((circlePoints P q).card:ℝ))⁻¹

private theorem mass_le_retained_add_loss (P Q C : Finset Plane) (H : P×P → Finset Q)
    (he : 0 < incidences P Q)
    (hcover : ∀ z : P×P, ¬circleSafe P z → ∃ c∈C,dist (z.1:Plane) c=1 ∧ dist (z.2:Plane) c=1) :
    goodTripleMass (unitRows P Q) H (incidences P Q) ≤
      goodTripleMass (unitRows P Q) (removeRichPairs H) (incidences P Q) + lossSum P Q C := by
  let forbidden (p r : Plane) := ∃ c∈C,dist p c=1 ∧ dist r c=1
  let k (q : Plane) := (incidences P Q*((circlePoints P q).card:ℝ))⁻¹
  have kpos (q : Plane) : 0 ≤ k q := by dsimp [k]; positivity
  have eqmass : lossSum P Q C = ∑ q : Q,∑ p ∈ unitRows P Q q, ∑ r ∈ unitRows P Q q,
      if forbidden p r then k q else 0 := by
    unfold lossSum
    rw [←Finset.sum_attach Q]
    apply sum_congr rfl
    intro q _
    rw [sum_unitRows P Q q (fun p => ∑ r ∈ unitRows P Q q, if forbidden p r then k q else 0)]
    apply sum_congr rfl
    intro p _
    rw [sum_filter,sum_unitRows P Q q (fun r => if forbidden p r then k q else 0)]
  have deg (q : Q) : ((unitRows P Q q).card:ℝ) = (circlePoints P q).card :=
    unitRows_center_degree P Q q
  rw [goodTripleMass_center_sum _ _ he, goodTripleMass_center_sum _ _ he,eqmass,←sum_add_distrib]
  apply sum_le_sum
  intro q _
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro p _
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro r _
  rw [deg]
  by_cases h : circleSafe P (p,r)
  · simp only [removeRichPairs,if_pos h]
    by_cases hf : forbidden p r <;> by_cases hq : q∈H (p,r) <;> simp [hf,hq,kpos q]
  · have hf : forbidden p r := hcover (p,r) h
    simp only [removeRichPairs,if_neg h,notMem_empty,if_false,if_pos hf,zero_add]
    split_ifs
    · exact le_rfl
    · exact kpos q

/-- Uniformly in the winning piece and the event carried by its triples, the
absolute mass discarded tends to zero. The test for retention uses |P|^(9/10),
so it directly supplies the circle requirement in AdmissibleGraph. -/
theorem rich_circle_loss_eventually {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t : ℝ in atTop, ∀ (P Q : Finset Plane) (M : CommonFieldModel.Model P Q),
      ProofAssembly.LargePiece t P Q M → ∀ H : P×P → Finset Q,
        goodTripleMass (unitRows P Q) H (incidences P Q) <
          goodTripleMass (unitRows P Q) (removeRichPairs H) (incidences P Q) + η := by
  let g := 3*exactGap
  let a := 10000*g
  have hg : 0 < g := mul_pos (by norm_num) exactGap_pos
  have ha : a ≤ 1/100 := by
    have hb := exactGap_lt_largeHeightGap.trans_le
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (by norm_num : (-(594036:ℝ)) ≤ -(32:ℝ)))
    rw [Real.rpow_neg (by norm_num),← Nat.cast_ofNat (R := ℝ) (n:=32),Real.rpow_natCast] at hb
    norm_num1 at hb
    dsimp [a,g]
    linarith
  have neg1 : -3/5+6*a+100*g < 0 := by dsimp [a] at *; linarith
  have neg2 : -9/5+3*a+100*g < 0 := by dsimp [a] at *; linarith
  have neg3 : -a+90*g < 0 := by dsimp [a]; linarith
  have small (k x : ℝ) (hx : x < 0) : Tendsto (fun t : ℝ => k*t^x) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (neg_pos.mpr hx)).const_mul k
    simpa only [neg_neg,mul_zero] using h
  have dec := ((small 256 _ neg1).add (small 16 _ neg2)).add (small (2/(27/50)) _ neg3)
  simp only [add_zero] at dec
  filter_upwards [dec.eventually (eventually_lt_nhds hη), eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (by norm_num : 0 < (9/10:ℝ))).eventually_ge_atTop 2] with t decay ht htwo
  have ht0 := zero_lt_one.trans_le ht
  intro P Q M pie H
  obtain ⟨_,pLo,pHi,_,edge,dp,_,dq,_,_,_⟩ := pie
  let A := t^(-1-2*a+100*g)
  let B := t^(-2-a+100*g)
  let d := (27/50:ℝ)*t^(a-90*g)
  let e := incidences P Q
  let m := ⌈t^(9/10:ℝ)⌉₊
  have he : 0 < e := (Real.rpow_pos_of_pos ht0 _).trans_le edge
  have hd : 0 < d := by dsimp [d]; positivity
  have hm : 2 ≤ m := by exact_mod_cast htwo.trans (Nat.le_ceil _)
  let hf := (rich_circles_finite_count P hm).1
  let C := hf.toFinset
  have centers (c : Plane) : c∈C ↔ m ≤ (circlePoints P c).card := hf.mem_toFinset
  have cHi : (C.card:ℝ) ≤ 16*t^(1/5+4*a) := by
    rw [show C.card=(richCenterSet P m).ncard from (Set.ncard_eq_toFinset_card _ hf).symm]
    exact rich_circles_power_bound P ht0 htwo pHi
  have c2 : ((P.filter (fun p => 2 ≤ (circlePoints C p).card)).card:ℝ) ≤ (C.card:ℝ)^2 := by
    have h := double_covered_points_count P C
    rw [offDiag_card] at h
    exact_mod_cast (h.trans (by rw [pow_two]; exact Nat.sub_le _ _) : _ ≤ C.card^2)
  have safeCover (z : P×P) (hz : ¬circleSafe P z) :
      ∃ c∈C,dist (z.1:Plane) c=1 ∧ dist (z.2:Plane) c=1 := by
    unfold circleSafe at hz
    push Not at hz
    obtain ⟨c,hp,hr,hcard⟩ := hz
    refine ⟨c,(centers _).2 (Nat.ceil_le.mpr (le_trans ?_ hcard)),hp,hr⟩
    apply Real.rpow_le_rpow ht0.le _ (by norm_num)
    have hle : (1:ℝ) ≤ 1+2*a-173*g := by dsimp [a]; linarith
    exact le_trans (by simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le ht hle)) pLo
  have atom (p : Plane) (hp : p∈P) :
      ((Q.filter fun q => p∈circlePoints P q).card:ℝ)/e ≤ A := by
    have hh : Q.filter (fun q => p∈circlePoints P q) = Q.filter (fun q => dist q p=1) := by
      ext q; simp [hp,dist_comm p]
    rw [hh]
    exact (dp p hp).2.2.2
  have catom (q : Plane) (hq : q∈Q) : ((circlePoints P q).card:ℝ)/e ≤ B := by
    have h := div_le_div₀ (Real.rpow_nonneg ht0.le _) (dq q hq).2.1 (Real.rpow_pos_of_pos ht0 _) edge
    rw [←Real.rpow_sub ht0] at h
    apply h.trans_eq
    change t^(a+10*g-(2+2*a-90*g)) = t^(-2-a+100*g)
    congr 1; ring
  have cost := rich_circle_deletion_cost P Q C (circlePoints P) he hd
    (fun q hq => (dq q hq).1) rfl (fun _ _ => filter_subset ..)
    (fun _ _ _ h => (mem_circlePoints.mp h).2) atom catom
  have term1 : ((P.filter (fun p => 2 ≤ (circlePoints C p).card)).card:ℝ)*A ≤
      256*t^(-3/5+6*a+100*g) := by
    have hh := (mul_le_mul_of_nonneg_right (c2.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) cHi 2))
      (Real.rpow_nonneg ht0.le (-1-2*a+100*g)))
    apply hh.trans_eq
    rw [mul_pow,show (16:ℝ)^2=256 by norm_num,pow_two,mul_assoc,←Real.rpow_add ht0,←Real.rpow_add ht0]
    congr 2; ring
  have term2 : (C.card:ℝ)*B ≤ 16*t^(-9/5+3*a+100*g) := by
    apply (mul_le_mul_of_nonneg_right cHi (Real.rpow_nonneg ht0.le _)).trans_eq
    rw [mul_assoc,←Real.rpow_add ht0]
    congr 2; ring
  have term3 : 2/d = (2/(27/50:ℝ))*t^(-a+90*g) := by
    dsimp [d]
    rw [show -a+90*g = -(a-90*g) by ring,Real.rpow_neg ht0.le]
    ring
  have lost : lossSum P Q C < η :=
    ((cost.trans (add_le_add (add_le_add term1 term2) term3.le))).trans_lt decay
  exact (mass_le_retained_add_loss P Q C H he safeCover).trans_lt (add_lt_add_right lost _)

/-- Manuscript scale selection and rich-circle deletion use the same sampled
triples. Removing rich pairs retains the claimed absolute mass ε/16000 as
soon as the supplied scale event has mass at least ε/8000. -/
theorem rich_circle_survival {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ (P Q : Finset Plane) (M : CommonFieldModel.Model P Q),
      ProofAssembly.LargePiece t P Q M → ∀ H : P×P → Finset Q,
        ε/8000 ≤ goodTripleMass (unitRows P Q) H (incidences P Q) →
        ε/16000 ≤ goodTripleMass (unitRows P Q) (removeRichPairs H) (incidences P Q) := by
  filter_upwards [rich_circle_loss_eventually (div_pos hε (by norm_num : (0:ℝ)<16000))]
    with t ht
  intro P Q M h H hmass
  linarith [ht P Q M h H]

namespace ProofAssembly


end ProofAssembly
end
end PlanarUnitDistances
