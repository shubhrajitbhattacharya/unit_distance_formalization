import PlanarUnitDistances.CrossComparisons

/-! Second common-level inequality with the actual posterior of the same-history law. Adapted from OAI RareEvents. -/
namespace OAI
namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X : Type*} [Fintype X]
lemma event_markov (μ : Law X) (f : X → ℝ) (hf : ∀x,0≤f x) {ε : ℝ} (hε : 0<ε) :
    event μ (fun x => ε<f x)≤avg μ f/ε := by
  apply (le_div_iff₀ hε).mpr
  rw [mul_comm]; unfold event; rw [←avg_smul]
  apply avg_mono
  intro x
  split_ifs with h
  · simpa using h.le
  · simpa using hf x
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.CommonTemplate
open Finset FiniteLaw FiniteStarCoupling StrictCross CrossSampling CrossStructure FiniteMarginalScore
open scoped Classical
noncomputable section
variable {P Q H A B : Type*} [Fintype P] [Fintype Q] [Fintype H] [Fintype A] [Fintype B]
def posteriorState (π : Law (P×Q)) (h : P → H) (x : P → A×B) (v : H) : Law (A×B) :=
  push (cond (left π) h v) x

def predictionError (π : Law (P×Q)) (h : P → H) (x : P → A×B) (y : Q → A×B) : ℝ :=
  avg π (fun pq => 1-crossMass (posteriorState π h x (h pq.1)) (y pq.2))

omit [Fintype H] in

theorem marginal_score (π : Law (P×Q)) (h : P → H) (bit : P → Q → Bool)
    (x : P → A×B) (y : Q → A×B) {ε : ℝ} (hε : 0<ε) :
    VP π bit/6≤DP π bit y+avg (left π) (fun p => tau (posteriorState π h x (h p)))+
      16*(event π (fun pq => ¬Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))+
        predictionError π h x y/ε+ε) := by
  let good : P → Q → Prop := fun p q => Consistent (bit p q) (x p) (y q) ∧
    1-ε≤crossMass (posteriorState π h x (h p)) (y q)
  have hs := avg_mono (left π) (fun p => second_slice (row π p) (bit p) y
    (posteriorState π h x (h p)) (x p) (good p) hε.le
    (fun _ hg => hg.1) (fun _ hg => hg.2))
  simp only [avg_sub,div_eq_mul_inv,avg_add,avg_smul,avg_const] at hs
  have hv : avg (left π) (fun p => StarScore.variation (row π p) (bit p)*6⁻¹)=VP π bit*6⁻¹ := by
    simp [VP,avg,Finset.sum_mul,mul_assoc]
  rw [hv,row_event] at hs
  have hb : event π (fun pq => ¬good pq.1 pq.2)≤
      event π (fun pq => ¬Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))+
      predictionError π h x y/ε := by
    refine (event_mono π ?_).trans ((event_union_le π _ _).trans (add_le_add_right
      (event_markov π (fun pq => 1-crossMass (posteriorState π h x (h pq.1)) (y pq.2))
        (fun pq => sub_nonneg.mpr (event_le_one _ _)) hε) _))
    intro pq hg
    by_cases hc : Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2)
    · right
      have hn : ¬1-ε≤crossMass (posteriorState π h x (h pq.1)) (y pq.2) := fun hp => hg ⟨hc,hp⟩
      linarith
    · exact Or.inl hc
  change _≤DP π bit y+_ at hs
  linarith
end
end PlanarUnitDistances.CommonTemplate


end OAI
