import PlanarUnitDistances.FlankCharge
import PlanarUnitDistances.BalancedWindow
import PlanarUnitDistances.CrossScores
import PlanarUnitDistances.ThresholdProfiles

namespace PlanarUnitDistances.Flanks
open Set MeasureTheory Real OAI.PlanarUnitDistances
open scoped Classical
noncomputable section

def bothOne (b b' : ℝ) (wMatch : ℝ → Prop) (s : ℝ) := s<b ∧ s<b' ∧ wMatch s
def bothZero (b b' : ℝ) (zMatch : ℝ → Prop) (s : ℝ) := b ≤ s ∧ b' ≤ s ∧ zMatch s
def commonPositive (lo hi ε b b' : ℝ) (f g : ℝ → ℝ) (zMatch wMatch : ℝ → Prop) (s : ℝ) :=
  if s∈commonRegion lo hi ε f ∧ (bothOne b b' wMatch s ∨ bothZero b b' zMatch s)
  then StrictCross.coefficient (g s) else 0
def rarePositive (lo hi ε b b' : ℝ) (f : ℝ → ℝ) (zMatch wMatch keep : ℝ → Prop) (s : ℝ) :=
  if (s∈Icc lo hi ∧ keep s ∧ f s<ε ∧ bothOne b b' wMatch s) ∨
      (s∈Icc lo hi ∧ keep s ∧ 1-ε<f s ∧ bothZero b b' zMatch s) then (2:ℝ) else 0
def positive (lo hi ε b b' : ℝ) (f g : ℝ → ℝ) (zMatch wMatch keep : ℝ → Prop) (s : ℝ) :=
  rarePositive lo hi ε b b' f zMatch wMatch keep s+commonPositive lo hi ε b b' f g zMatch wMatch s

/-- The fixed-pair calculation, using literal direct and reciprocal matches,
the actual coefficient of the conditional bias, and the complete bit
disagreement. The exceptional/good test is arbitrary in this upper bound. -/
theorem sorted_slot_bound {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {d d' : K}
    (hd : d≠0) (hd' : d'≠0) (hne : d≠d') (ord : BudgetPlaces.threshold v d ≤ BudgetPlaces.threshold v d')
    {lo hi ε c l r : ℝ} (he : ε≤1/2) (hT : 0≤BudgetPlaces.alpha v d d'+c)
    {f g : ℝ → ℝ} (hf : Antitone f)
    (win : balancedRegion lo hi ε (1/sqrt 24) f g ⊆ Icc l r)
    (zMatch wMatch keep : ℝ → Prop)
    (hz : ∀s,zMatch s → v (d-d')≤exp (-s+c)) (hw : ∀s,wMatch s → v (d⁻¹-d'⁻¹)≤exp (s+c))
    (hint : Integrable (positive lo hi ε (BudgetPlaces.threshold v d) (BudgetPlaces.threshold v d')
      f g zMatch wMatch keep)) :
    (∫s,positive lo hi ε (BudgetPlaces.threshold v d) (BudgetPlaces.threshold v d') f g zMatch wMatch keep s)-
      |BudgetPlaces.threshold v d-BudgetPlaces.threshold v d'| ≤
      BudgetPlaces.flankCharge v c d d'+(1/6:ℝ)*
      (if BudgetPlaces.threshold v d∈Ioo l r ∧ BudgetPlaces.threshold v d'∈Ioo l r then max 0 (r-l) else 0) := by
  let b := BudgetPlaces.threshold v d
  let b' := BudgetPlaces.threshold v d'
  let T := BudgetPlaces.alpha v d d'+c
  let A := fun s => s∈Icc lo hi ∧ keep s ∧ f s<ε ∧ bothOne b b' wMatch s
  let B := fun s => s∈Icc lo hi ∧ keep s ∧ 1-ε<f s ∧ bothZero b b' zMatch s
  have leftInt (s : ℝ) (h : bothOne b b' wMatch s) : s∈Icc (b-T) b :=
    BudgetPlaces.reciprocal_match_lower_flank v hd hd' hne ord h.1 (hw s h.2.2)
  have rightInt (s : ℝ) (h : bothZero b b' zMatch s) : s∈Icc b' (b'+T) :=
    BudgetPlaces.direct_match_upper_flank v hne ord h.2.1 (hz s h.2.2)
  have cap (s : ℝ) (hh : commonPositive lo hi ε b b' f g zMatch wMatch s≠0) :
      ε≤f s ∧ f s≤1-ε ∧ (s∈Icc (b-T) b ∨ s∈Icc b' (b'+T)) ∧
      commonPositive lo hi ε b b' f g zMatch wMatch s≤(if s∈Icc l r then 1+1/6 else 1-1/6) := by
    unfold commonPositive at hh ⊢
    split_ifs at hh with h
    · rw [if_pos h]
      refine ⟨h.1.2.1,h.1.2.2,h.2.imp (leftInt s) (rightInt s),?_⟩
      unfold StrictCross.coefficient
      by_cases bal : |g s-1/2|≤1/sqrt 24
      · rw [if_pos bal,if_pos (win ⟨h.1,bal⟩)]
      · rw [if_neg bal]; split_ifs <;> norm_num
    · exact (hh rfl).elim
  have eqp (s : ℝ) (D : Decidable (A s ∨ B s)) :
      (@ite ℝ (A s ∨ B s) D 2 0)+commonPositive lo hi ε b b' f g zMatch wMatch s =
      positive lo hi ε b b' f g zMatch wMatch keep s := by
    unfold positive rarePositive
    by_cases h : A s ∨ B s
    · rw [if_pos h]
      dsimp only [A,B] at h
      rw [if_pos h]
    · rw [if_neg h]
      dsimp only [A,B] at h
      rw [if_neg h]
  have p := antitone_level_budget hf ord hT he (by norm_num : (0:ℝ)≤1/6)
    (by norm_num : (1/6:ℝ)≤1) A B (commonPositive lo hi ε b b' f g zMatch wMatch)
    (fun s h => ⟨leftInt s h.2.2.2,h.2.2.1⟩) (fun s h => ⟨rightInt s h.2.2.2,h.2.2.1⟩) cap
    (by simp_rw [eqp]; exact hint)
  simp_rw [eqp] at p
  change (∫s,positive lo hi ε b b' f g zMatch wMatch keep s) ≤ 2*T+_ at p
  change (∫s,positive lo hi ε b b' f g zMatch wMatch keep s)-|b-b'|≤_+_
  unfold BudgetPlaces.flankCharge
  change _ ≤ 2*T-(max b b'-min b b')+_
  rw [max_eq_right ord,min_eq_left ord,abs_of_nonpos (sub_nonpos.mpr ord)]
  linarith only [p]

end
end PlanarUnitDistances.Flanks
