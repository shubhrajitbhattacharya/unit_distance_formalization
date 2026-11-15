import PlanarUnitDistances.UniformIncidenceLaw
import PlanarUnitDistances.PosteriorWidth
import PlanarUnitDistances.GeometricLargeProfile

namespace PlanarUnitDistances.UniformPhysical
open Finset MeasureTheory NumberField OAI.PlanarUnitDistances
open FiniteLaw FiniteStarCoupling CommonTemplate PhysicalLevels
open UniformNormalization EdgeHeightScale BoundedHeight
open scoped Classical
noncomputable section
variable {P Q : Type} [Fintype P] [Fintype Q] {K : Type*} [Field K] [NumberField K]

theorem edge_information (S : Q → Finset P) (e : ℝ) (he : 0<e) (ht : ∑q,((S q).card:ℝ)=e)
    (hne : ∀q,(S q).Nonempty) : commonInformation (edgeLaw S e he ht)=twoEdgeInformation S e := by
  let ν := edgeLaw S e he ht
  have rk : (right ν).val = centerLaw S e := funext (edge_right S e he ht)
  have rkpos (q : Q) : 0<(right ν).val q := by
    rw [rk]; exact div_pos (Nat.cast_pos.mpr (card_pos.mpr (hne q))) he
  have cols : (fun q => (col ν q).val)=neighborLaw S := by
    funext q p
    rw [col_val ν (rkpos q) p,rk]
    change weight S e p q / centerLaw S e q = neighborLaw S q p
    by_cases h : p∈S q <;> simp [weight,centerLaw,neighborLaw,hne,h,div_eq_mul_inv]
    field_simp [he.ne',Nat.cast_ne_zero.mpr (card_ne_zero.mpr (hne q))]
  have hm : FiniteInformation.marginal (right ν).val (fun q => (col ν q).val) = (FiniteStarCoupling.left ν).val :=
    congrArg Law.val (mixture_left ν)
  unfold commonInformation twoEdgeInformation
  change FiniteInformation.KL (FiniteInformation.wedge (right ν).val _) _ = _
  rw [←hm,rk,cols]

def primes (S : Q → Finset P) (z w : P⊕Q → K) : Finset (FinitePlace K) :=
  (radius_finite_support S z w).toFinset

lemma radius_zero (S : Q → Finset P) (z w : P⊕Q → K) {v : FinitePlace K} (hv : v∉primes S z w) :
    profileRadius S z w v.1 = 0 := by
  by_contra h
  exact hv ((Set.Finite.mem_toFinset _).mpr h)

def fullMeasure (S : Q → Finset P) (z w : P⊕Q → K) (U V : InfinitePlace K → ℝ×ℝ) :=
  let r := profileRadius S z w
  measure (primes S z w) z w U V (fun v => -r v.1) (fun v => r v.1) (fun v => -r v.1) (fun v => r v.1)
instance (S : Q → Finset P) (z w : P⊕Q → K) (U V : InfinitePlace K → ℝ×ℝ) :
    IsFiniteMeasure (fullMeasure S z w U V) := by unfold fullMeasure; infer_instance

theorem full_off_diagonal (S : Q → Finset P) (z w : P⊕Q → K)
    (hz : Function.Injective (z ∘ Sum.inl)) (hw : Function.Injective (w ∘ Sum.inl))
    (U V : InfinitePlace K → ℝ×ℝ) {p q : P} (hn : p≠q) :
    (∫ j, PredictionCut.pairScore (j.x p) (j.x q) ∂fullMeasure S z w U V) ≤ Real.log 2 := by
  have h₁ : z (.inl p)≠z (.inl q) := fun he => hn (hz he)
  have h₂ : w (.inl p)≠w (.inl q) := fun he => hn (hw he)
  have bounds (v : AbsoluteValue K ℝ) := (radius_bounds S z w v).2 p q
  have hr (v : AbsoluteValue K ℝ) : -profileRadius S z w v≤profileRadius S z w v :=
    neg_le_self (le_trans (abs_nonneg _) (bounds v).1)
  apply posterior_pair_bound _ _ _ _ _ _ _ _ _ h₁ h₂ _ (fun v => hr v.1)
    (fun v => neg_le_neg ((le_abs_self _).trans (bounds v.1).1)) (fun v => (le_abs_self _).trans (bounds v.1).2)
    (fun v _ => hr v.1) (fun v _ => neg_le_neg ((le_abs_self _).trans (bounds v.1).1))
    (fun v _ => (le_abs_self _).trans (bounds v.1).2)
  intro v hv
  have bd := bounds v.1
  rw [radius_zero S z w hv] at bd
  have one (u : K) (h : u≠0) (hh : |Real.log (v.1 u)|≤0) : v u=1 := by
    have lg : Real.log (v.1 u)=0 := abs_nonpos_iff.mp hh
    exact (Real.exp_log (v.1.pos h)).symm.trans (by rw [lg,Real.exp_zero])
  rw [map_mul,one _ (sub_ne_zero.mpr h₁) bd.1,one _ (sub_ne_zero.mpr h₂) bd.2,mul_one]

omit [NumberField K] in
private lemma minority_make (S : Q → Finset P) (e : ℝ) (he : 0<e) (ht : ∑q,((S q).card:ℝ)=e)
    (z : P⊕Q → K) (v : AbsoluteValue K ℝ) (s : ℝ) (labs : P⊕Q → Finset (P⊕Q)×Finset (P⊕Q)) :
    PhysicalLevels.minority (edgeLaw S e he ht) (make labs (fun p q => decide (s < -Real.log (v (z (.inl p)-z (.inr q)))))) =
      ThresholdProfiles.minority (fun pq => weight S e pq.1 pq.2) (threshold v (direction S z)) s := by
  have eqv : event (edgeLaw S e he ht) (fun pq : P×Q => decide (s < -Real.log (v (z (.inl pq.1)-z (.inr pq.2))))=true) =
      ThresholdProfiles.frequency (fun pq => weight S e pq.1 pq.2) (threshold v (direction S z)) s := by
    unfold event avg ThresholdProfiles.frequency
    apply sum_congr rfl; intro pq _
    by_cases hp : pq.1∈S pq.2 <;> simp [edgeLaw,weight,direction,threshold,ThresholdProfiles.bit,hp]
  exact congrArg (fun a => min a (1-a)) eqv

/-- The S in the score estimates equals the minority-profile scale that is
already produced by the bounded-height obstruction for this same edge set. -/
theorem full_scale (S : Q → Finset P) (e : ℝ) (he : 0<e) (ht : ∑q,((S q).card:ℝ)=e)
    (z w : P⊕Q → K) (U V : InfinitePlace K → ℝ×ℝ) :
    (∫j, PhysicalLevels.minority (edgeLaw S e he ht) j ∂fullMeasure S z w U V) =
      profileScale S e z (fun v => -profileRadius S z w v) (profileRadius S z w) := by
  unfold fullMeasure
  rw [integral_measure]
  have ha (v : InfinitePlace K) (s : ℝ) :
      PhysicalLevels.minority (edgeLaw S e he ht) (arch v (U v) (V v) z w s) =
        ThresholdProfiles.minority (fun pq => weight S e pq.1 pq.2) (threshold v.1 (direction S z)) s :=
    minority_make S e he ht z v.1 s _
  have hb (v : FinitePlace K) (s : ℝ) :
      PhysicalLevels.minority (edgeLaw S e he ht) (PhysicalLevels.finite v z w s) =
        ThresholdProfiles.minority (fun pq => weight S e pq.1 pq.2) (threshold v.1 (direction S z)) s :=
    minority_make S e he ht z v.1 s _
  simp_rw [ha,hb]
  unfold profileScale placeSum minorityIntegral
  congr 2
  symm
  apply finsum_eq_sum_of_support_subset
  intro v hv
  by_contra hn
  simp [radius_zero S z w hn] at hv

end
end PlanarUnitDistances.UniformPhysical
