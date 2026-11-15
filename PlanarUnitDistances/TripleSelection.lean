import PlanarUnitDistances.RichCircleSurvival
import PlanarUnitDistances.Selection

namespace PlanarUnitDistances.ProofAssembly
open Filter OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence Finset
open scoped Classical Topology
noncomputable section

abbrev UnitTriple (P Q : Finset Plane) := (P×P)×Q

/-- The original experiment has mass 1/(e deg(q)) on each triple consisting
of an ordered pair of neighbors of q; all other triples have mass zero. -/
def tripleWeight (P Q : Finset Plane) (x : UnitTriple P Q) : ℝ :=
  if x.1.1 ∈ unitRows P Q x.2 ∧ x.1.2 ∈ unitRows P Q x.2 then
    (incidences P Q * degree P x.2)⁻¹ else 0

theorem tripleWeight_nonneg (P Q : Finset Plane) (x : UnitTriple P Q) : 0 ≤ tripleWeight P Q x := by
  dsimp [tripleWeight]
  split_ifs
  · exact inv_nonneg.mpr (mul_nonneg (incidences_nonneg P Q) (degree_nonneg P _))
  · exact le_rfl

private theorem restrict_sum {A : Type*} [Fintype A] [DecidableEq A] (s : Finset A) (f : A → ℝ) :
    (∑ x ∈ s,f x) = ∑ x,if x∈s then f x else 0 := by rw [←sum_filter]; simp

def tripleEventCenters (P Q : Finset Plane) (E : UnitTriple P Q → Prop) (z : P×P) : Finset Q :=
  univ.filter fun q => 0 < tripleWeight P Q (z,q) ∧ E (z,q)

theorem mem_tripleEventCenters (P Q : Finset Plane) (E : UnitTriple P Q → Prop) (z : P×P) (q : Q) :
    q ∈ tripleEventCenters P Q E z ↔ 0 < tripleWeight P Q (z,q) ∧ E (z,q) := by
  simp [tripleEventCenters]

/-- Reindex any tested subset of the triples into exactly its pair-centered
fibers. No untested or nonincident triple acquires probability. -/
theorem tripleWeight_event (P Q : Finset Plane) (E : UnitTriple P Q → Prop) (he : 0 < incidences P Q) :
    (∑ x, if E x then tripleWeight P Q x else 0) =
      goodTripleMass (unitRows P Q)
        (tripleEventCenters P Q E) (incidences P Q) := by
  unfold tripleEventCenters
  rw [goodTripleMass_center_sum _ _ he,Fintype.sum_prod_type,sum_comm]
  apply sum_congr rfl
  intro q _
  rw [Fintype.sum_prod_type]
  simp_rw [restrict_sum (unitRows P Q q)]
  apply sum_congr rfl
  intro p _
  by_cases hp : p∈unitRows P Q q
  · rw [if_pos hp]
    apply sum_congr rfl
    intro r _
    by_cases hr : r∈unitRows P Q q
    · have hdeg : (0:ℝ)<degree P q := by
        rw [←unitRows_center_degree P Q q]; exact_mod_cast card_pos.mpr ⟨p,hp⟩
      have hv := mul_pos (inv_pos.mpr hdeg) (inv_pos.mpr he)
      simp [hp,hr,tripleWeight,unitRows_center_degree,hv]
    · simp [hp,hr,tripleWeight]
  · simp [hp,tripleWeight]

theorem tripleWeight_total (P Q : Finset Plane) (he : 0 < incidences P Q) :
    ∑ x,tripleWeight P Q x = 1 := by
  rw [Fintype.sum_prod_type,sum_comm]
  have hq (q : Q) : (∑ z : P×P,tripleWeight P Q (z,q)) = degree P q / incidences P Q := by
    rw [Fintype.sum_prod_type]
    have hcut : (∑ p : P,∑ r : P,tripleWeight P Q ((p,r),q)) =
       ∑ _p ∈ unitRows P Q q, ∑ _r ∈ unitRows P Q q,(incidences P Q*degree P q)⁻¹ := by
      simp_rw [restrict_sum (unitRows P Q q)]
      apply sum_congr rfl
      intro p _
      by_cases hp : p∈unitRows P Q q <;> simp [tripleWeight,hp]
    rw [hcut]
    simp only [sum_const,nsmul_eq_mul,unitRows_center_degree]
    by_cases hd : degree P q=0
    · simp [hd]
    · field_simp
  simp only [hq,←sum_div,←unitRows_center_degree,unitRows_total,div_self he.ne']

/-- S is the integrated minority mass for the original directions of this
very model and the same intervals as in LargePiece. -/
def pieceScale {P Q : Finset Plane} (M : CommonFieldModel.Model P Q) : ℝ :=
  let r := profileRadius (unitRows P Q) M.z M.w
  UniformNormalization.profileScale (unitRows P Q) (incidences P Q) M.z (fun v => -r v) r

def pairWidth {P Q : Finset Plane} (H : P → ℝ) (x : UnitTriple P Q) : ℝ := H x.1.1+H x.1.2

/-- The precise three integral estimates and the pointwise signed/unsigned
comparison needed before the one-scale theorem. H is a point-only width,
V is a point-only endpoint vector, and Z is the triple error. -/
def ComparisonMoments {P Q : Finset Plane} (M : CommonFieldModel.Model P Q) : Prop :=
  let S := pieceScale M
  let m := tripleWeight P Q
  ∃ (H : P → ℝ) (V : P → HeightPlace M.field → ℝ) (Z : UnitTriple P Q → ℝ),
    (∀ p,0 ≤ H p) ∧ (∀ p,FiniteAtPrimes (V p)) ∧ (∀ x,0 ≤ Z x) ∧
    2*S/203 < ∑ x,m x*pairWidth H x ∧
    (∑ x,m x*(if 8*S/comparisonEpsilon < pairWidth H x then pairWidth H x else 0)) ≤
      (2:ℝ)^14/2^144*S ∧
    (∑ x,m x*Z x) ≤ (2:ℝ)^12/2^144*S ∧
    ∀ x,0 < m x →
      let l := centerRatio M x.1.1 x.1.2 x.2
      pairWidth H x-Z x ≤ placeNorm (localLog l) ∧
      placeNorm (localLog l-(V x.1.2-V x.1.1)) ≤ Z x

/-- The selected pre-deletion event with its lower bound on the very same scale. -/
def BeforeCircleDeletionAtScale {P Q : Finset Plane} (M : CommonFieldModel.Model P Q) (minScale : ℝ) : Prop :=
  ∃ (J : ℝ) (V : P → HeightPlace M.field → ℝ) (centers : P×P → Finset Q),
    minScale ≤ J ∧ 12*2^111 ≤ J ∧ (∀ p, FiniteAtPrimes (V p)) ∧
    comparisonEpsilon/8000 ≤ goodTripleMass (unitRows P Q) centers (incidences P Q) ∧
    ∀ z q, q ∈ centers z →
      z.1 ≠ z.2 ∧ z.1 ∈ unitRows P Q q ∧ z.2 ∈ unitRows P Q q ∧
      J/3 ≤ weilHeight (centerRatio M z.1 z.2 q) ∧
      placeNorm (localLog (centerRatio M z.1 z.2 q) - (V z.2-V z.1)) ≤ J/(648*2^111)

/-- Selection of J on the original walk from its moment bounds. Every
surviving fiber uses J, V, Z and the very same center in both inequalities. -/
theorem before_circle_deletion_at_scale_of_moments {P Q : Finset Plane} (M : CommonFieldModel.Model P Q)
    {t : ℝ} (ht : 0<t) (piece : LargePiece t P Q M) (mom : ComparisonMoments M) :
    BeforeCircleDeletionAtScale M (pieceScale M/500) := by
  let S := pieceScale M
  let m := tripleWeight P Q
  obtain ⟨_,_,_,_,ed,_,_,_,_,_,large⟩ := piece
  have he := lt_of_lt_of_le (Real.rpow_pos_of_pos ht _) ed
  have hS : (2:ℝ)^2100 < S := large
  have hS0 : 0 < S := (by positivity : (0:ℝ) < 2^2100).trans hS
  have hε : 0 < comparisonEpsilon := by unfold comparisonEpsilon; positivity
  obtain ⟨H,V,Z,hH,hV,hZ,hmean,htail,herr,comp⟩ := mom
  let W := pairWidth (Q:=Q) H
  obtain ⟨J,hJ,hm⟩ := exists_height_scale m W Z S comparisonEpsilon hS0 hε
    (tripleWeight_nonneg P Q) (tripleWeight_total P Q he) (fun x => add_nonneg (hH _) (hH _))
    hZ hmean htail herr
  have hbig : (12:ℝ)*2^111 ≤ J := by
    have hh : (2:ℝ)^124 ≤ 2^2100 := pow_le_pow_right₀ (by norm_num) (by decide)
    have hn : (12:ℝ)*2^111*500 ≤ 2^124 := by norm_num
    exact (le_div_iff₀ (by norm_num : (0:ℝ)<500)).2 (hn.trans (hh.trans hS.le)) |>.trans hJ.1
  let E (x : UnitTriple P Q) := J≤W x ∧ W x≤2*J ∧ Z x≤J/(648*2^111)
  let C := tripleEventCenters P Q E
  refine ⟨J,V,C,hJ.1,hbig,hV,?_,?_⟩
  · apply hm.trans_eq
    dsimp only [C]
    rw [←tripleWeight_event P Q E he]
    apply sum_congr rfl; intro x _
    by_cases hx : E x <;> simp only [E] at hx <;> simp [E,m,hx]
  intro z q hq
  obtain ⟨positive,hwlo,_,hz⟩ := (mem_tripleEventCenters P Q E z q).mp hq
  have inci : z.1 ∈ unitRows P Q q ∧ z.2 ∈ unitRows P Q q := by
    by_contra h
    have hz0 : m (z,q)=0 := by simp [m,tripleWeight,h]
    linarith
  let l := centerRatio M z.1 z.2 q
  have spec := centerRatio_spec M inci.1 inci.2
  have eqheight : 2*weilHeight l = placeNorm (localLog l) := twice_weilHeight_eq_absLog spec.1
  have ⟨hunsigned,hsigned⟩ := comp (z,q) positive
  change W (z,q)-Z (z,q) ≤ placeNorm (localLog l) at hunsigned
  have hpos : 0 < J := lt_of_lt_of_le (by positivity : (0:ℝ)<12*2^111) hbig
  have hthird : J/(648*2^111) ≤ J/3 := by
    apply div_le_div_of_nonneg_left hpos.le (by norm_num) (by norm_num)
  have height : J/3 ≤ weilHeight l := by linarith
  have distinct : z.1 ≠ z.2 := by
    intro same
    have nz : M.z (.inl z.2)-M.z (.inr q) ≠ 0 :=
      left_ne_zero_of_mul_eq_one (M.unit_identity _ _ (mem_filter.mp inci.2).2)
    have hz1 : l=1 := by simp [l,centerRatio,same,nz]
    rw [hz1,weilHeight_one] at height
    linarith
  exact ⟨distinct,inci.1,inci.2,height,hsigned.trans hz⟩


end
end PlanarUnitDistances.ProofAssembly