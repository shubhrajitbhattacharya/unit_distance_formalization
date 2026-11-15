import PlanarUnitDistances.PosteriorWidth
import PlanarUnitDistances.RareCoupling

namespace OAI.PlanarUnitDistances.PhysicalLevels
open Finset MeasureTheory FiniteLaw FiniteStarCoupling TemplateCoupling CommonTemplate RareScore
open scoped Classical
noncomputable section
variable {P Q Θ : Type*} [Fintype P] [Fintype Q] [Fintype Θ]

def goodRare (π : Law (P×Q)) := {t : Record P Q | ¬common π t ∧ good π t}
def badRare (π : Law (P×Q)) := {t : Record P Q | ¬common π t ∧ ¬good π t}
def rareIntegral (π : Law (P×Q)) (ν : Measure (Record P Q)) (g v : Record P Q → ℝ) :=
  (∫ t in goodRare π,g t ∂ν) - (∫ t in badRare π,v t ∂ν)

private theorem rare_int_lower (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν]
    (b n j m g v : Record P Q → ℝ) (h : ∀t,2*(b t-n t)-4*j t-6*m t ≤ g t)
    (hv : ∀t,v t≤1) (hm : ∀t,0 ≤ m t) (hm' : (∫t,m t ∂ν)≤4) :
    2*((∫ t in goodRare π,b t ∂ν)-(∫ t in goodRare π,n t ∂ν))-
      4*(∫ t in goodRare π,j t ∂ν)-24-ν.real (badRare π) ≤ rareIntegral π ν g v := by
  have main := integral_mono (μ:=ν.restrict (goodRare π))
    (Integrable.of_finite (f:=fun t => 2*(b t-n t)-4*j t-6*m t)) Integrable.of_finite h
  simp only [integral_sub Integrable.of_finite Integrable.of_finite,integral_const_mul] at main
  have M := (integral_mono_measure (μ:=ν.restrict (goodRare π)) Measure.restrict_le_self
    (Filter.Eventually.of_forall hm) Integrable.of_finite).trans hm'
  have V := integral_mono (μ:=ν.restrict (badRare π)) Integrable.of_finite
    (Integrable.of_finite (f:=fun _ => (1:ℝ))) hv
  rw [setIntegral_one_eq_measureReal] at V
  unfold rareIntegral
  linarith only [main,M,V]

/-- The good- and bad-rare contributions of Q, P and T on a single measure.
The third contribution uses the very same list kernel at every occurrence.
Joint-exception mass J is still explicit here. -/
theorem rare_integrals (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν]
    (a : Q → Law Θ) (r : Record P Q → Bool) (l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q))
    (hm : (∫t,inconsistency π t.bit t.x t.y ∂ν)≤4) :
    let x := fun t : Record P Q => pointException π (r t) (l t) t.x
    let y := fun t : Record P Q => centerException π (r t) (l t) t.y
    let j := fun t : Record P Q => jointException π (r t) (l t) t.x t.y
    let X := ∫ t in goodRare π,x t ∂ν
    let Y := ∫ t in goodRare π,y t ∂ν
    let E := 4*(∫ t in goodRare π,j t ∂ν)+24+ν.real (badRare π)
    2*(Y-X)-E ≤ rareIntegral π ν (fun t => centerScore π (r t) (l t) t.x t.y t.bit) (fun t => VQ π t.bit) ∧
    2*(X-Y)-E ≤ rareIntegral π ν (fun t => pointScore π (r t) (l t) t.x t.y t.bit) (fun t => VP π t.bit) ∧
    2*(X-Y)-E ≤ rareIntegral π ν
      (fun t => avg (templates π a) (fun θ => pointScore (slice π a θ) (r t) (l t) t.x t.y t.bit))
      (fun t => avg (templates π a) (fun θ => VP (slice π a θ) t.bit)) := by
  let m := fun t : Record P Q => inconsistency π t.bit t.x t.y
  have hnn (t : Record P Q) : 0 ≤ m t := event_nonneg ..
  have Q := rare_int_lower π ν _ _ _ m _ _ (fun t => center_lower π (r t) (l t) t.x t.y t.bit)
    (fun t => (vq_le π t.bit).trans (by norm_num)) hnn hm
  have P := rare_int_lower π ν _ _ _ m _ _ (fun t => point_lower π (r t) (l t) t.x t.y t.bit)
    (fun t => (vp_le π t.bit).trans (by norm_num)) hnn hm
  have T := rare_int_lower π ν _ _ _ m _ _ (fun t => list_lower π a (r t) (l t) t.x t.y t.bit)
    (fun t => avg_le_const (templates π a) (fun θ => (vp_le (slice π a θ) t.bit).trans (by norm_num))) hnn hm
  dsimp only
  constructor
  · linarith only [Q]
  constructor
  · linarith only [P]
  · linarith only [T]

end
end OAI.PlanarUnitDistances.PhysicalLevels
