import PlanarUnitDistances.FlankSlot

namespace PlanarUnitDistances.Flanks
open Set MeasureTheory Finset Real OAI.PlanarUnitDistances
open scoped Classical
noncomputable section

private theorem positive_swap (lo hi ε b b' : ℝ) (f g : ℝ → ℝ) (z w k : ℝ → Prop) :
    positive lo hi ε b b' f g z w k = positive lo hi ε b' b f g z w k := by
  funext s
  have one : bothOne b b' w s ↔ bothOne b' b w s := by simp only [bothOne]; tauto
  have zero : bothZero b b' z s ↔ bothZero b' b z s := by simp only [bothZero]; tauto
  simp only [positive,rarePositive,commonPositive,one,zero]

/-- The same two-interval bound holds for the iid ordered pair in its
sampled order, even when the thresholds are in decreasing order. -/
theorem unsorted_slot_bound {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {d d' : K}
    (hd : d≠0) (hd' : d'≠0) (hne : d≠d') {lo hi ε c l r : ℝ} (he : ε≤1/2)
    (hT : 0≤BudgetPlaces.alpha v d d'+c) {f g : ℝ → ℝ} (hf : Antitone f)
    (win : balancedRegion lo hi ε (1/sqrt 24) f g ⊆ Icc l r)
    (z w k : ℝ → Prop) (hz : ∀s,z s → v (d-d')≤exp (-s+c))
    (hw : ∀s,w s → v (d⁻¹-d'⁻¹)≤exp (s+c))
    (hint : Integrable (positive lo hi ε (BudgetPlaces.threshold v d) (BudgetPlaces.threshold v d') f g z w k)) :
    (∫s,positive lo hi ε (BudgetPlaces.threshold v d) (BudgetPlaces.threshold v d') f g z w k s)-
      |BudgetPlaces.threshold v d-BudgetPlaces.threshold v d'| ≤
      BudgetPlaces.flankCharge v c d d'+(1/6:ℝ)*
      (if BudgetPlaces.threshold v d∈Ioo l r ∧ BudgetPlaces.threshold v d'∈Ioo l r then max 0 (r-l) else 0) := by
  by_cases ord : BudgetPlaces.threshold v d≤BudgetPlaces.threshold v d'
  · exact sorted_slot_bound v hd hd' hne ord he hT hf win z w k hz hw hint
  have swap (a b : K) : v (b-a)=v (a-b) := by rw [←neg_sub a b,v.map_neg]
  have aeq : BudgetPlaces.alpha v d' d=BudgetPlaces.alpha v d d' := by
    simp only [BudgetPlaces.alpha,BudgetPlaces.threshold,swap d d',min_comm]
  have ceq : BudgetPlaces.flankCharge v c d' d=BudgetPlaces.flankCharge v c d d' := by
    simp only [BudgetPlaces.flankCharge,aeq,max_comm,min_comm]
  have posEq := positive_swap lo hi ε (BudgetPlaces.threshold v d') (BudgetPlaces.threshold v d) f g z w k
  have result := sorted_slot_bound v hd' hd hne.symm (le_of_not_ge ord) he (by rwa [aeq]) hf win z w k
    (fun s h => (swap d d').trans_le (hz s h)) (fun s h => (swap d⁻¹ d'⁻¹).trans_le (hw s h))
    (by rwa [posEq])
  simpa only [posEq,abs_sub_comm (BudgetPlaces.threshold v d') (BudgetPlaces.threshold v d),
    ceq,and_comm] using result

/-- Average the sorted-pair estimate over the two independent samples at a
fixed original base. The off-diagonal display retains the actual local
logarithmic correction for that pair. The only geometric premises are the
pointwise direct and reciprocal bounds on a coordinate match and
nonnegativity of the flank width for distinct neighbors. -/
theorem iid_distinct_upper {K I : Type*} [Field K] [Fintype I] (v : AbsoluteValue K ℝ)
    (μ : I → ℝ) (hμ : ∀ i,0≤μ i) (total : ∑ i,μ i=1)
    (d : I → K) (hn : ∀i,d i≠0) (inj : Function.Injective d)
    {lo hi ε c : ℝ} (he : ε≤1/2) (f : ℝ → ℝ) (hf : Antitone f)
    (z w k : I → I → ℝ → Prop)
    (flank : ∀i j,i≠j → 0≤BudgetPlaces.alpha v (d i) (d j)+c)
    (hz : ∀i j s,z i j s → v (d i-d j)≤exp (-s+c))
    (hw : ∀i j s,w i j s → v ((d i)⁻¹-(d j)⁻¹)≤exp (s+c))
    (hint : ∀i j,i≠j → Integrable (positive lo hi ε (BudgetPlaces.threshold v (d i))
      (BudgetPlaces.threshold v (d j)) f (thresholdTail μ (BudgetPlaces.threshold v ∘ d))
      (z i j) (w i j) (k i j))) :
    let Z := BudgetPlaces.threshold v ∘ d
    let g := thresholdTail μ Z
    (∑i,∑j,if i=j then 0 else μ i*μ j*((∫s,positive lo hi ε (Z i) (Z j) f g
      (z i j) (w i j) (k i j) s)-|Z i-Z j|-BudgetPlaces.flankCharge v c (d i) (d j)))
      ≤ (1/15:ℝ)*∫s in commonRegion lo hi ε f,2*g s*(1-g s) := by
  intro Z g
  obtain ⟨l,r,win,_,charge⟩ := finite_balanced_window μ Z hμ total lo hi ε hf
  apply le_trans _ charge
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have nonneg := mul_nonneg (hμ i) (hμ j)
  have leng := le_max_left (0:ℝ) (r-l)
  by_cases eq : i=j
  · rw [if_pos eq]
    split_ifs <;> positivity
  · rw [if_neg eq]
    have upper := unsorted_slot_bound v (hn i) (hn j) (inj.ne eq) he (flank i j eq) hf win
      (z i j) (w i j) (k i j) (hz i j) (hw i j) (hint i j eq)
    change (∫s,positive lo hi ε (Z i) (Z j) f g (z i j) (w i j) (k i j) s)-|Z i-Z j| ≤
      BudgetPlaces.flankCharge v c (d i) (d j)+(1/6:ℝ)*
      (if Z i∈Ioo l r ∧ Z j∈Ioo l r then max 0 (r-l) else 0) at upper
    by_cases inside : Z i∈Ioo l r ∧ Z j∈Ioo l r
    · rw [if_pos inside] at upper ⊢
      nlinarith only [mul_le_mul_of_nonneg_left upper nonneg]
    · rw [if_neg inside] at upper ⊢
      nlinarith only [mul_le_mul_of_nonneg_left upper nonneg]

end
end PlanarUnitDistances.Flanks
