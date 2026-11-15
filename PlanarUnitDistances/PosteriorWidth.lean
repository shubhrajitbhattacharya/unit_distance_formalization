import PlanarUnitDistances.PhysicalLevels
import PlanarUnitDistances.ExactCommonScores

namespace OAI.PlanarUnitDistances.PhysicalLevels
open Finset MeasureTheory FiniteLaw FiniteStarCoupling CommonTemplate
open _root_.PlanarUnitDistances.ComparisonConstants
open scoped Classical
noncomputable section
variable {P Q H : Type*} [Fintype P] [Fintype Q] [Fintype H]

def minority (π : Law (P×Q)) (t : Record P Q) :=
  let p := event π (fun pq => t.bit pq.1 pq.2=true)
  min p (1-p)
def common (π : Law (P×Q)) (t : Record P Q) := dy 1800 ≤ minority π t
def good (π : Law (P×Q)) (t : Record P Q) := inconsistency π t.bit t.x t.y ≤ dy 1800

def width (ν : Measure (Record P Q)) (f : Record P Q → Prop) := ∫ t, RareScore.ind (f t) ∂ν

lemma width_tail (ν : Measure (Record P Q)) [IsFiniteMeasure ν] (f : Record P Q → ℝ)
    (h₀ : ∀t,0≤f t) (A : Record P Q → Prop) {ε : ℝ} (hε : 0<ε) (hb : ∀ t, A t → ε≤f t) :
    width ν A ≤ (∫ t,f t ∂ν)/ε := by
  have hh := integral_mono (μ := ν) (Integrable.of_finite (f := fun t => RareScore.ind (A t)))
    (Integrable.of_finite (f := fun t => f t/ε)) (fun t => show RareScore.ind (A t) ≤ f t/ε from by
      by_cases h : A t
      · simpa [RareScore.ind,h] using (one_le_div hε).mpr (hb t h)
      · simpa [RareScore.ind,h] using div_nonneg (h₀ t) hε.le)
  rwa [integral_div] at hh

lemma common_width (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν] :
    width ν (common π) ≤ (∫t,minority π t ∂ν)/dy 1800 :=
  width_tail ν _ (fun _ => le_min (event_nonneg ..) (sub_nonneg.mpr (event_le_one ..)))
    _ (pos _) (fun _ h => h)
lemma bad_width (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν]
    (hm : (∫t,inconsistency π t.bit t.x t.y ∂ν) ≤ 4) :
    width ν (fun t => ¬common π t ∧ ¬good π t) ≤ 4/dy 1800 :=
  (width_tail ν _ (fun _ => event_nonneg ..) _ (pos _)
    (fun _ h => (lt_of_not_ge h.2).le)).trans (div_le_div_of_nonneg_right hm (pos _).le)

def pointWidth (π : Law (P×Q)) (ν : Measure (Record P Q)) (r : Record P Q → Bool)
    (label : Record P Q → Finset (P⊕Q) × Finset (P⊕Q)) :=
  avg (left π) (fun p => width ν (fun t => ¬common π t ∧ good π t ∧ RareScore.exceptional (r t) (label t) (t.x p)))

private lemma one_plus_four {a : ℝ} (ha : 1≤a) : 1+4*a≤8*a := by linarith

private lemma cutoff_constants {S W b a : ℝ} (hS : 2^2100<S) (hW : 0≤W) (hw : W≤S/dy 1800)
    (hbad : b≤4/dy 1800) (ha : a≤dy 144000) :
    Real.log 2 + b + W*a ≤ dy 144*S := by
  have hs : 0<S := (pow_pos (by norm_num : (0:ℝ)<2) 2100).trans hS
  have hh := mul_le_mul_of_nonneg_right hS.le (pos 145).le
  have poweq : (2:ℝ)^2100*dy 145=2^1955 := by
    rw [show (2100:ℕ)=1955+145 by decide,pow_add,dy,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ (two_ne_zero : (2:ℝ)≠0)),mul_one]
  rw [poweq] at hh
  have large := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by decide : 1803≤1955)
  have mid : (2:ℝ)^1803=8*(2:ℝ)^1800 := by rw [show (1803:ℕ)=3+1800 by decide,pow_add]; norm_num1; rfl
  rw [mid] at large
  have hlog : Real.log 2≤1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have h4 : 4/dy 1800=4*(2:ℝ)^1800 := by rw [dy,div_eq_mul_inv,inv_inv]
  rw [h4] at hbad
  have main : Real.log 2+b ≤ S*dy 145 := calc
    _ ≤ 1+4*(2:ℝ)^1800 := add_le_add hlog hbad
    _ ≤ 8*(2:ℝ)^1800 := by
      let A := (2:ℝ)^1800
      change 1+4*A ≤ 8*A
      have hA : 1≤A := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
      exact one_plus_four hA
    _ ≤ _ := large.trans hh
  have correction : W*a ≤ S*dy 145 := calc
    _ ≤ W*dy 144000 := mul_le_mul_of_nonneg_left ha hW
    _ ≤ (S/dy 1800)*dy 144000 := mul_le_mul_of_nonneg_right hw (pos _).le
    _ = S*dy (144000-1800) := by rw [←div 144000 1800 (by decide)]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (antitone (by decide)) hs.le
  have hhalf : dy 145=dy 144/2 := by
    have e := mul 144 1
    change dy 144 * dy 1=dy 145 at e
    rw [←e,show dy 1=(1/2:ℝ) from by norm_num [dy]]; ring
  rw [hhalf] at main correction
  linarith only [main,correction]

/-- The posterior comparison, using the same record law for all levels and the
same-history pair. Width bounds are deduced from the definition of the good and
common levels and the integrated edge inconsistency bound. -/
theorem posterior_comparison (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν]
    (h : P → H) (r : Record P Q → Bool) (label : Record P Q → Finset (P⊕Q)×Finset (P⊕Q))
    (hp : ∀p q : P,p≠q → (∫t,PredictionCut.pairScore (t.x p) (t.x q) ∂ν) ≤ Real.log 2)
    {θ : ℝ} (hθ : 0≤θ) (hmarg : ∀p,(left π).val p≤θ)
    (hsize : (Fintype.card H:ℝ)*θ ≤ dy 144000)
    (hm : (∫t,inconsistency π t.bit t.x t.y ∂ν) ≤ 4)
    (hS : 2^2100 < ∫t,minority π t ∂ν) :
    (∫t, (if common π t then posteriorMoment π h t else 0) ∂ν) ≤
      2*pointWidth π ν r label + dy 144*(∫t,minority π t ∂ν) := by
  have core := PredictionCut.integrated (left π) h ν (common π) (good π) r label
    (fun t => t.x) (Real.log 2) (Real.log_nonneg (by norm_num))
    Integrable.of_finite Integrable.of_finite (fun _ => Integrable.of_finite)
    (fun _ _ => Integrable.of_finite) (fun _ _ => Integrable.of_finite) hp hθ hmarg
  have eqv (t : Record P Q) :
      avg (PredictionCoupling.coupling (left π) h) (fun pp =>
        if common π t then PredictionCut.pairScore (t.x pp.1) (t.x pp.2) else 0) =
      if common π t then posteriorMoment π h t else 0 := by
    by_cases hc : common π t
    · simp only [if_pos hc]
      exact PredictionCoupling.tau_eq (left π) h t.x
    · simp [hc,avg_const]
  simp_rw [eqv] at core
  have ee := cutoff_constants hS (integral_nonneg (fun t => RareScore.ind_nonneg (common π t)))
    (common_width π ν) (bad_width π ν hm) hsize
  change _ ≤ Real.log 2+2*pointWidth π ν r label+_+_ at core
  unfold width at ee
  linarith only [core,ee]

end
end OAI.PlanarUnitDistances.PhysicalLevels
