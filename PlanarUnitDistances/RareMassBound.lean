import PlanarUnitDistances.RareDominant

namespace OAI.PlanarUnitDistances.PhysicalLevels
open Finset FiniteLaw FiniteStarCoupling CommonTemplate RareScore MeasureTheory
open _root_.PlanarUnitDistances.ComparisonConstants
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

lemma pointWidth_integral (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν]
    (r : Record P Q → Bool) (l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)) :
    (∫t in goodRare π,pointException π (r t) (l t) t.x ∂ν)=pointWidth π ν r l := by
  have ex (t : Record P Q) : pointException π (r t) (l t) t.x =
      avg (left π) (fun p => ind (exceptional (r t) (l t) (t.x p))) := by
    rw [left,push_avg]; rfl
  simp_rw [ex]
  rw [FiniteLawIntegral.integral_avg _ _ (fun _ => Integrable.of_finite)]
  apply avg_congr
  intro p
  rw [←integral_indicator (Set.toFinite _).measurableSet]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  by_cases hc : common π t <;> by_cases hg : good π t <;>
    simp [goodRare,Set.indicator,ind,hc,hg]

def centerWidth (π : Law (P×Q)) (ν : Measure (Record P Q))
    (r : Record P Q → Bool) (l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)) :=
  avg (right π) (fun q => width ν (fun t => ¬common π t ∧ good π t ∧ exceptional (r t) (l t) (t.y q)))

lemma centerWidth_integral (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν]
    (r : Record P Q → Bool) (l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)) :
    (∫t in goodRare π,centerException π (r t) (l t) t.y ∂ν)=centerWidth π ν r l := by
  have ex (t : Record P Q) : centerException π (r t) (l t) t.y =
      avg (right π) (fun q => ind (exceptional (r t) (l t) (t.y q))) := by
    rw [right,push_avg]; rfl
  simp_rw [ex]
  rw [FiniteLawIntegral.integral_avg _ _ (fun _ => Integrable.of_finite)]
  apply avg_congr
  intro q
  rw [←integral_indicator (Set.toFinite _).measurableSet]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  by_cases hc : common π t <;> by_cases hg : good π t <;>
    simp [goodRare,Set.indicator,ind,hc,hg]

private lemma dy_radical : (4*dy 1800)^(2/25:ℝ) ≤ 2*dy 144 := by
  have h : 0≤4*dy 1800 := mul_nonneg (by norm_num) (pos _).le
  apply le_of_pow_le_pow_left₀ (n:=25) (by decide) (mul_nonneg (by norm_num) (pos _).le)
  calc
    ((4*dy 1800)^(2/25:ℝ))^25 = (4*dy 1800)^2 := by
      rw [←Real.rpow_natCast ((4*dy 1800)^(2/25:ℝ)) 25,←Real.rpow_mul h,
        show (2/25:ℝ)*(25:ℕ)=(2:ℕ) by norm_num,Real.rpow_natCast]
    _ = 4^2*dy 3600 := by rw [mul_pow,pow]
    _ ≤ 2^25*dy 3600 := mul_le_mul_of_nonneg_right (by norm_num) (pos _).le
    _ = (2*dy 144)^25 := by rw [mul_pow,pow]

lemma joint_rare (π : Law (P×Q)) {ξ : ℝ} (E : RectangleLaw π ξ) (hξ : 0≤ξ)
    (t : Record P Q) (ht : t∈goodRare π) (r : Bool) (l : Finset (P⊕Q)×Finset (P⊕Q))
    (hdom : pointException π r l t.x+centerException π r l t.y≤2*(minority π t+inconsistency π t.bit t.x t.y)) :
    jointException π r l t.x t.y ≤
      (2*dy 144+ξ)*(pointException π r l t.x+centerException π r l t.y) := by
  let F := fun p => exceptional r l (t.x p)
  let G := fun q => exceptional r l (t.y q)
  let u := event E.U F
  let v := event E.V G
  let H := pointException π r l t.x+centerException π r l t.y
  let b := Real.sqrt (u*v)
  have U : 0≤u := event_nonneg ..
  have V : 0≤v := event_nonneg ..
  have am : b ≤ (u+v)/2 := by
    dsimp [b]
    rw [Real.sqrt_mul U]
    nlinarith only [sq_nonneg (Real.sqrt u-Real.sqrt v),Real.sq_sqrt U,Real.sq_sqrt V]
  have lp := E.lowP F
  have lq := E.lowQ G
  change (27/50:ℝ)*u≤pointException π r l t.x at lp
  change (27/50:ℝ)*v≤centerException π r l t.y at lq
  have hH : b≤H := by dsimp only [H]; linarith only [am,lp,lq,U,V]
  have hmi : minority π t<dy 1800 := lt_of_not_ge ht.1
  have hm : inconsistency π t.bit t.x t.y≤dy 1800 := ht.2
  have bsmall : b≤4*dy 1800 := by
    change b≤pointException π r l t.x+centerException π r l t.y at hH
    linarith only [hH,hmi,hm,hdom]
  have br := (Real.rpow_le_rpow (Real.sqrt_nonneg _) bsmall (by norm_num : (0:ℝ)≤2/25)).trans dy_radical
  exact (E.rect F G).trans ((mul_le_mul hH (add_le_add br le_rfl)
    (add_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) hξ) ((Real.sqrt_nonneg _).trans hH)).trans_eq (mul_comm ..))

private lemma restricted_positive (ν : Measure (Record P Q)) [IsFiniteMeasure ν] (A : Set (Record P Q))
    (f : Record P Q → ℝ) (hf : ∀t,0≤f t) : (∫t in A,f t ∂ν)≤∫t,f t ∂ν :=
  integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall hf) Integrable.of_finite

/-- A concrete dominant-label assignment on all good rare records. Its
integrated endpoint masses and joint-edge exception use the very same
assignment at every point and center. -/
theorem rare_masses (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν] {ξ : ℝ}
    (E : RectangleLaw π ξ) (hξ : 0≤ξ) (hx : ξ≤dy 146)
    (hm : (∫t,inconsistency π t.bit t.x t.y ∂ν)≤4) (hs : 4≤∫t,minority π t ∂ν) :
    ∃l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q),
    let H := fun t : Record P Q => pointException π (rareBit π t) (l t) t.x+centerException π (rareBit π t) (l t) t.y
    let J := fun t : Record P Q => jointException π (rareBit π t) (l t) t.x t.y
    (∀t∈goodRare π,H t≤2*(minority π t+inconsistency π t.bit t.x t.y)) ∧
    (∫t in goodRare π,H t ∂ν) ≤ 4*(∫t,minority π t ∂ν) ∧
    (∫t in goodRare π,J t ∂ν) ≤ 9*(dy 144*(∫t,minority π t ∂ν)) := by
  have hξ100 : ξ≤1/(2:ℝ)^100 := by simpa only [dy,one_div] using hx.trans (antitone (by decide : 100≤146))
  obtain ⟨l,hdom⟩ := choose_dominant π E hξ hξ100
  refine ⟨l,hdom,?_⟩
  let S := ∫t,minority π t ∂ν
  let H := fun t : Record P Q => pointException π (rareBit π t) (l t) t.x+centerException π (rareBit π t) (l t) t.y
  let A := goodRare π
  have hM := (restricted_positive ν A (fun t => inconsistency π t.bit t.x t.y) (fun _ => event_nonneg ..)).trans hm
  have hF := restricted_positive ν A (minority π)
    (fun _ => le_min (event_nonneg ..) (sub_nonneg.mpr (event_le_one ..)))
  have hInt := setIntegral_mono_on (μ:=ν) (f:=H)
    Integrable.of_finite Integrable.of_finite (Set.toFinite A).measurableSet hdom
  change (∫t in A,H t ∂ν) ≤ ∫t in A,2*(minority π t+inconsistency π t.bit t.x t.y) ∂ν at hInt
  rw [integral_const_mul,integral_add (f:=minority π) (g:=fun t => inconsistency π t.bit t.x t.y) Integrable.of_finite Integrable.of_finite] at hInt
  have upper : (∫t in A,H t ∂ν)≤4*S := by
    dsimp only [S]
    linarith only [hInt,hM,hF,hs]
  refine ⟨upper,?_⟩
  let c := 2*dy 144+ξ
  have hc : 0≤c := add_nonneg (mul_nonneg (by norm_num) (pos _).le) hξ
  have hJ := setIntegral_mono_on (μ:=ν) Integrable.of_finite Integrable.of_finite
    (Set.toFinite A).measurableSet (fun t ht => joint_rare π E hξ t ht (rareBit π t) (l t) (hdom t ht))
  rw [integral_const_mul] at hJ
  have h4 : 4*dy 146=dy 144 := by
    have h := mul 144 2
    change dy 144*dy 2=dy 146 at h
    rw [←h,show dy 2=(1/4:ℝ) by norm_num [dy]]; ring
  have hh : c*4≤9*dy 144 := by
    dsimp only [c]; linarith only [hx,h4]
  have t0 : 0≤S := (by norm_num : (0:ℝ)≤4).trans hs
  have mm := mul_le_mul_of_nonneg_right hh t0
  exact hJ.trans ((mul_le_mul_of_nonneg_left upper hc).trans
    (by change c*(4*S)≤9*(dy 144*S); rw [←mul_assoc,←mul_assoc]; exact mm))

private lemma bad_budget {S W : ℝ} (hS : 2^2100<S) (hW : W≤4/dy 1800) :
    24+W≤dy 144*S := by
  have hs := mul_le_mul_of_nonneg_left hS.le (pos 144).le
  have e1 : dy 144*(2:ℝ)^2100=2^1956 := by
    rw [show (2100:ℕ)=144+1956 by decide,pow_add,←mul_assoc]
    change ((2:ℝ)^144)⁻¹*(2:ℝ)^144*(2:ℝ)^1956=(2:ℝ)^1956
    rw [inv_mul_cancel₀ (pow_ne_zero _ (two_ne_zero : (2:ℝ)≠0)),one_mul]
  have e2 : (2:ℝ)^1804=16*(2:ℝ)^1800 := by rw [show (1804:ℕ)=4+1800 by decide,pow_add]; norm_num1; rfl
  have big := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by decide : 1804≤1956)
  have two : (2:ℝ)≤(2:ℝ)^1800 := by
    simpa only [pow_one] using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by decide : 1≤1800))
  rw [e1] at hs
  rw [e2] at big
  rw [dy,div_eq_mul_inv,inv_inv] at hW
  have aux {a w : ℝ} (ha : 2≤a) (hw : w≤4*a) : 24+w≤16*a := by linarith
  exact (aux two hW).trans (big.trans hs)

/-- The paper allows 64 e0 S in the three rare bounds. The same dominant
assignment gives the stronger 37 e0 S under the displayed graph hypotheses. -/
theorem rare_error_budget (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν] {ξ : ℝ}
    (E : RectangleLaw π ξ) (hξ : 0≤ξ) (hx : ξ≤dy 146)
    (hm : (∫t,inconsistency π t.bit t.x t.y ∂ν)≤4) (hs : 2^2100<∫t,minority π t ∂ν) :
    ∃l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q),
      (∀t∈goodRare π,pointException π (rareBit π t) (l t) t.x+centerException π (rareBit π t) (l t) t.y
        ≤2*(minority π t+inconsistency π t.bit t.x t.y)) ∧
      4*(∫t in goodRare π,jointException π (rareBit π t) (l t) t.x t.y ∂ν)+24+ν.real (badRare π)
        ≤37*(dy 144*(∫t,minority π t ∂ν)) := by
  have four : (4:ℝ)≤(2:ℝ)^2100 := by
    have hu := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by decide : 2≤2100)
    norm_num1 at hu
    exact hu
  obtain ⟨l,hdom,_,hj⟩ := rare_masses π ν E hξ hx hm (four.trans hs.le)
  have hw : ν.real (badRare π)≤4/dy 1800 := by
    rw [←integral_indicator_one (Set.toFinite _).measurableSet]
    exact bad_width π ν hm
  refine ⟨l,hdom,?_⟩
  have calcBound {j b e : ℝ} (hj : j≤9*e) (hb : 24+b≤e) : 4*j+24+b≤37*e := by linarith
  exact calcBound hj (bad_budget hs hw)

end
end OAI.PlanarUnitDistances.PhysicalLevels
