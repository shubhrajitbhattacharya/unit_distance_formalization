/- Local identities adapted from OpenAI math, UnitDistances/States.lean,
   adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0).
   The global identity is stated for all number fields, using Mathlib places. -/
import Mathlib

namespace OAI
namespace PlanarUnitDistances.BudgetPlaces
open Real Finset
open scoped BigOperators
noncomputable section

variable {K : Type*} [Field K]

def threshold (v : AbsoluteValue K ℝ) (d : K) : ℝ := -log (v d)
def alpha (v : AbsoluteValue K ℝ) (d d' : K) : ℝ :=
  threshold v (d-d')-min (threshold v d) (threshold v d')
def differenceProduct (d d' : K) : K := (d-d')*(d⁻¹-d'⁻¹)

lemma differenceProduct_ne_zero {d d' : K} (h : d ≠ d') :
    differenceProduct d d' ≠ 0 :=
  mul_ne_zero (sub_ne_zero.mpr h) (sub_ne_zero.mpr (inv_injective.ne h))

lemma inv_difference_abs (v : AbsoluteValue K ℝ) {d d' : K}
    (hd : d ≠ 0) (hd' : d' ≠ 0) :
    v (d⁻¹-d'⁻¹) = v (d-d')/(v d*v d') := by
  have he : d⁻¹-d'⁻¹ = -(d-d')/(d*d') := by field_simp; ring
  rw [he,map_div₀,v.map_neg,v.map_mul]

theorem place_identity (v : AbsoluteValue K ℝ) {d d' : K}
    (hd : d ≠ 0) (hd' : d' ≠ 0) (hdd : d ≠ d') :
    -log (v (differenceProduct d d')) =
      2*alpha v d d'-(max (threshold v d) (threshold v d')-
        min (threshold v d) (threshold v d')) := by
  have hD := v.pos (sub_ne_zero.mpr hdd)
  have hdv := v.pos hd
  have hdv' := v.pos hd'
  have hI := v.pos (sub_ne_zero.mpr (inv_injective.ne hdd))
  rw [differenceProduct,v.map_mul,log_mul hD.ne' hI.ne',inv_difference_abs v hd hd',
    log_div hD.ne' (mul_ne_zero hdv.ne' hdv'.ne'),log_mul hdv.ne' hdv'.ne']
  unfold alpha threshold
  have hm := min_add_max (-log (v d)) (-log (v d'))
  linarith

lemma alpha_nonneg_nonarch (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {d d' : K} (hd : d ≠ 0) (hd' : d' ≠ 0) (hdd : d ≠ d') :
    0 ≤ alpha v d d' := by
  have hD := v.pos (sub_ne_zero.mpr hdd)
  have htri : v (d-d') ≤ max (v d) (v d') := by
    simpa only [sub_eq_add_neg,v.map_neg] using hv d (-d')
  unfold alpha threshold
  by_cases hh : v d ≤ v d'
  · rw [max_eq_right hh] at htri
    have hlog := log_le_log (v.pos hd) hh
    rw [min_eq_right (by linarith)]
    linarith [log_le_log hD htri]
  · have hh' := (le_of_not_ge hh)
    rw [max_eq_left hh'] at htri
    have hlog := log_le_log (v.pos hd') hh'
    rw [min_eq_left (by linarith)]
    linarith [log_le_log hD htri]

lemma alpha_add_log_two_nonneg (v : AbsoluteValue K ℝ)
    {d d' : K} (hd : d ≠ 0) (hd' : d' ≠ 0) (hdd : d ≠ d') :
    0 ≤ alpha v d d'+log 2 := by
  have hD := v.pos (sub_ne_zero.mpr hdd)
  have htri : v (d-d') ≤ v d+v d' := by
    simpa only [sub_eq_add_neg,v.map_neg] using v.add_le d (-d')
  unfold alpha threshold
  by_cases hh : v d ≤ v d'
  · have hlog := log_le_log (v.pos hd) hh
    have ht : v (d-d') ≤ 2*v d' := by linarith
    have hLt := log_le_log hD ht
    rw [log_mul (by norm_num : (2:ℝ) ≠ 0) (v.pos hd').ne'] at hLt
    rw [min_eq_right (by linarith)]
    linarith
  · have hh' := (le_of_not_ge hh)
    have hlog := log_le_log (v.pos hd') hh'
    have ht : v (d-d') ≤ 2*v d := by linarith
    have hLt := log_le_log hD ht
    rw [log_mul (by norm_num : (2:ℝ) ≠ 0) (v.pos hd).ne'] at hLt
    rw [min_eq_left (by linarith)]
    linarith


/-- On a bit-one pair, a match in the reciprocal coordinate forces the level
into the lower flank, including on the boundary. -/
theorem reciprocal_match_lower_flank (v : AbsoluteValue K ℝ) {c s : ℝ} {d d' : K}
    (hd : d≠0) (hd' : d'≠0) (hdd : d≠d') (hord : threshold v d ≤ threshold v d')
    (hbit : s < threshold v d) (hmatch : v (d⁻¹-d'⁻¹) ≤ exp (s+c)) :
    s ∈ Set.Icc (threshold v d-(alpha v d d'+c)) (threshold v d) := by
  have hi := v.pos (sub_ne_zero.mpr (inv_injective.ne hdd))
  have hm := log_le_log hi hmatch
  rw [log_exp,inv_difference_abs v hd hd',log_div (v.pos (sub_ne_zero.mpr hdd)).ne'
    (mul_ne_zero (v.pos hd).ne' (v.pos hd').ne'),log_mul (v.pos hd).ne' (v.pos hd').ne'] at hm
  constructor
  · unfold alpha; rw [min_eq_left hord]; unfold threshold at hord ⊢; linarith
  · exact hbit.le

/-- On a bit-zero pair, a match in the direct coordinate forces the upper flank. -/
theorem direct_match_upper_flank (v : AbsoluteValue K ℝ) {c s : ℝ} {d d' : K}
    (hdd : d≠d') (hord : threshold v d ≤ threshold v d')
    (hbit : threshold v d' ≤ s) (hmatch : v (d-d') ≤ exp (-s+c)) :
    s ∈ Set.Icc (threshold v d') (threshold v d'+(alpha v d d'+c)) := by
  have hm := log_le_log (v.pos (sub_ne_zero.mpr hdd)) hmatch
  rw [log_exp] at hm
  refine ⟨hbit,?_⟩
  unfold alpha; rw [min_eq_left hord]; unfold threshold at hord ⊢; linarith

open NumberField
variable [NumberField K]

def flankCharge (v : AbsoluteValue K ℝ) (c : ℝ) (d d' : K) : ℝ :=
  2*(alpha v d d'+c)-(max (threshold v d) (threshold v d')-
    min (threshold v d) (threshold v d'))

omit [NumberField K] in
theorem flankCharge_eq (v : AbsoluteValue K ℝ) (c : ℝ) {d d' : K}
    (hd : d≠0) (hd' : d'≠0) (hdd : d≠d') :
    flankCharge v c d d'= -log (v (differenceProduct d d'))+2*c := by
  unfold flankCharge; linarith [place_identity v hd hd' hdd]

theorem normalized_flank_charge {d d' : K} (hd : d≠0) (hd' : d'≠0) (hdd : d≠d') :
    ((∑v : InfinitePlace K,(v.mult:ℝ)*flankCharge v.1 (log 2) d d')+
     ∑ᶠv : FinitePlace K,flankCharge v.1 0 d d')/(Module.finrank ℚ K:ℝ)=2*log 2 := by
  let y := differenceProduct d d'
  have hy : y≠0 := differenceProduct_ne_zero hdd
  have hi (v : InfinitePlace K) : 0 < v y := v.1.pos hy
  have hf (v : FinitePlace K) : 0 < v y := v.1.pos hy
  have hp := congrArg log (prod_abs_eq_one hy)
  have hi' : 0<(∏v : InfinitePlace K,v y^v.mult) := Finset.prod_pos (fun v _ => pow_pos (hi v) _)
  have hf' : 0<(∏ᶠv : FinitePlace K,v y) := by
    rw [finprod_eq_prod _ (FinitePlace.hasFiniteMulSupport hy)]
    exact Finset.prod_pos (fun v _ => hf v)
  rw [log_mul hi'.ne' hf'.ne',log_prod (fun v _ => (pow_pos (hi v) _).ne'),log_finprod hf,log_one] at hp
  simp only [log_pow] at hp
  have hI (v : InfinitePlace K) : flankCharge v.1 (log 2) d d' = -log (v y)+2*log 2 := flankCharge_eq v.1 _ hd hd' hdd
  have hF (v : FinitePlace K) : flankCharge v.1 0 d d' = -log (v y)+2*0 := flankCharge_eq v.1 _ hd hd' hdd
  simp_rw [hI,hF]
  change ((∑v : InfinitePlace K,(v.mult:ℝ)*(-log (v y)+2*log 2))+
    ∑ᶠ v : FinitePlace K,(-log (v y)+2*0))/(Module.finrank ℚ K:ℝ)=2*log 2
  simp only [mul_zero,add_zero,mul_add,mul_neg,Finset.sum_add_distrib,
    Finset.sum_neg_distrib,finsum_neg_distrib,←Finset.sum_mul] 
  have hm : (∑v : InfinitePlace K,(v.mult:ℝ))=(Module.finrank ℚ K:ℝ) := by
    exact_mod_cast (InfinitePlace.sum_mult_eq (K:=K))
  rw [hm]
  apply (div_eq_iff (Nat.cast_ne_zero.mpr (Module.finrank_pos (R:=ℚ) (M:=K)).ne')).mpr
  linarith

end
end PlanarUnitDistances.BudgetPlaces
end OAI
