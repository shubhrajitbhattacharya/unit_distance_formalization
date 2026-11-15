import PlanarUnitDistances.BinaryMinority
import PlanarUnitDistances.RareMassBound
import PlanarUnitDistances.Constants

namespace OAI.PlanarUnitDistances.PhysicalLevels
open FiniteLaw FiniteStarCoupling CommonTemplate RareScore CrossStructure MeasureTheory
open _root_.PlanarUnitDistances.ComparisonConstants
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

/-- The contribution from the rare minority bits can be charged to a single
chosen pair of labels and the actual partition inconsistency. -/
private theorem rare_minority (π : Law (P×Q)) (t : Record P Q)
    (l : Finset (P⊕Q)×Finset (P⊕Q)) :
    minority π t ≤ pointException π (rareBit π t) l t.x+
      centerException π (rareBit π t) l t.y+inconsistency π t.bit t.x t.y := by
  let A (e : P×Q) := exceptional (rareBit π t) l (t.x e.1)
  let B (e : P×Q) := exceptional (rareBit π t) l (t.y e.2)
  let C (e : P×Q) := ¬Consistent (t.bit e.1 e.2) (t.x e.1) (t.y e.2)
  rw [←minority_probability]
  have h : event π (fun e => t.bit e.1 e.2=rareBit π t)≤event π (fun e => (A e ∨ B e) ∨ C e) := by
    apply event_mono
    intro e hb
    by_cases h : Consistent (t.bit e.1 e.2) (t.x e.1) (t.y e.2)
    · exact Or.inl (minority_exception h hb)
    · exact Or.inr h
  exact (h.trans (event_union_le _ _ _)).trans (add_le_add (event_union_le π A B) (le_refl _))

/-- At all places together, the manuscript's full minority scale is bounded
by its two ordinary common comparisons and the widths for the same labels.
The bound holds for every choice of the rare label pair. -/
theorem scale_le_widths (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν]
    {ξ : ℝ} (E : RectangleLaw π ξ) (hξ : 0≤ξ) (hsmall : ξ≤1/(2:ℝ)^100)
    (hm : (∫t,inconsistency π t.bit t.x t.y ∂ν)≤4)
    (large : 2^2100<(∫t,minority π t ∂ν))
    (l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)) :
    (∫t,minority π t ∂ν) ≤
      10*((∫t in {t | common π t},VP π t.bit ∂ν)+(∫t in {t | common π t},VQ π t.bit ∂ν))+
      pointWidth π ν (rareBit π) l + centerWidth π ν (rareBit π) l +dy 144*(∫t,minority π t ∂ν) := by
  let C := {t : Record P Q | common π t}
  let G := goodRare π
  let B := badRare π
  let S := ∫t,minority π t ∂ν
  have parts : (∫t in C,minority π t ∂ν)+(∫t in G,minority π t ∂ν)+(∫t in B,minority π t ∂ν)=S := by
    have split : Cᶜ=G∪B := by ext t; simp [C,G,B,goodRare,badRare,←and_or_left] <;> tauto
    have disj : Disjoint G B := Set.disjoint_left.mpr (fun _ hg hb => hb.2 hg.2)
    have part := integral_add_compl (μ:=ν) (f:=minority π) (Set.toFinite C).measurableSet Integrable.of_finite
    rw [split,setIntegral_union disj (Set.toFinite B).measurableSet Integrable.of_finite Integrable.of_finite] at part
    simpa only [add_assoc] using part
  have commonBound := integral_mono (μ:=ν.restrict C) Integrable.of_finite Integrable.of_finite
    (fun t : Record P Q => BinaryMinority.minority_le_variations π E.U E.V E.rect E.lowP E.lowQ hξ hsmall t.bit)
  simp only [integral_const_mul,integral_add Integrable.of_finite Integrable.of_finite] at commonBound
  change (∫t in C,minority π t ∂ν)≤10*((∫t in C,VP π t.bit ∂ν)+(∫t in C,VQ π t.bit ∂ν)) at commonBound
  have rareBound := integral_mono (μ:=ν.restrict G) Integrable.of_finite Integrable.of_finite
    (fun t => rare_minority π t (l t))
  simp only [integral_add Integrable.of_finite Integrable.of_finite] at rareBound
  have pt := pointWidth_integral π ν (rareBit π) l
  have ct := centerWidth_integral π ν (rareBit π) l
  have inc := (integral_mono_measure (μ:=ν.restrict G) Measure.restrict_le_self
    (Filter.Eventually.of_forall (fun t : Record P Q => event_nonneg π (fun e => ¬Consistent (t.bit e.1 e.2) (t.x e.1) (t.y e.2)))) Integrable.of_finite).trans hm
  have smallMinor (t : Record P Q) : minority π t≤1 := (min_le_left ..).trans (event_le_one ..)
  have bb := integral_mono (μ:=ν.restrict B) Integrable.of_finite Integrable.of_finite smallMinor
  rw [setIntegral_one_eq_measureReal] at bb
  have wb := bad_width π ν hm
  have bmass : ν.real B=width ν (fun t => ¬common π t ∧ ¬good π t) := by
    unfold width
    symm
    exact integral_indicator_one (Set.toFinite B).measurableSet
  change (∫t in G,pointException π (rareBit π t) (l t) t.x ∂ν)=_ at pt
  change (∫t in G,centerException π (rareBit π t) (l t) t.y ∂ν)=_ at ct
  change (∫t in G,inconsistency π t.bit t.x t.y ∂ν)≤4 at inc
  rw [←bmass] at wb
  rw [pt,ct] at rareBound
  have budget : 4+4/dy 1800 ≤ dy 144*S := by
    have hh := mul_le_mul_of_nonneg_left large.le (pos 144).le
    have eq : dy 144*(2:ℝ)^2100=2^1956 := by
      rw [show (2100:ℕ)=144+1956 by decide,pow_add,dy,←mul_assoc,inv_mul_cancel₀ (by positivity),one_mul]
    rw [eq] at hh
    have cap := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by decide : 1803≤1956)
    rw [show (1803:ℕ)=3+1800 by decide,pow_add] at cap
    have arith (a : ℝ) (ha : 1≤a) : 4+4*a≤2^3*a := by linarith
    rw [dy,div_eq_mul_inv,inv_inv]
    exact (arith _ (one_le_pow₀ (by norm_num))).trans (cap.trans hh)
  change S ≤ 10*((∫t in C,VP π t.bit ∂ν)+(∫t in C,VQ π t.bit ∂ν))+_+_+dy 144*S
  linarith only [parts,commonBound,rareBound,inc,bb,wb,budget]

/-- Once the common-score and full-score comparisons give the three
inequalities of Proposition 6, the actual rare point width exceeds S/203. -/
theorem point_width_gt_of_comparisons (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν]
    {ξ : ℝ} (E : RectangleLaw π ξ) (hξ : 0≤ξ) (hsmall : ξ≤1/(2:ℝ)^100)
    (hm : (∫t,inconsistency π t.bit t.x t.y ∂ν)≤4)
    (large : 2^2100<(∫t,minority π t ∂ν))
    (l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)) :
    let S := ∫t,minority π t ∂ν
    let X := pointWidth π ν (rareBit π) l
    let Y := centerWidth π ν (rareBit π) l
    let cp := ∫t in {t | common π t},VP π t.bit ∂ν
    let cq := ∫t in {t | common π t},VQ π t.bit ∂ν
    cq ≤ 2048*(dy 144*S) → Y≤X+2048*(dy 144*S) → cp≤20*Y+1024*(dy 144*S) → S/203<X := by
  intro S X Y cp cq hq hy hp
  have sum := scale_le_widths π ν E hξ hsmall hm large l
  change S≤10*(cp+cq)+X+Y+dy 144*S at sum
  apply _root_.PlanarUnitDistances.exceptional_width_gt ((pow_pos (by norm_num : (0:ℝ)<2) 2100).trans large)
    (Y:=Y)
  · change S≤X+201*Y+30721*dy 144*S
    linarith
  · change Y≤X+2048*dy 144*S
    linarith

end
end OAI.PlanarUnitDistances.PhysicalLevels
