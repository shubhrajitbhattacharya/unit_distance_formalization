import PlanarUnitDistances.IntegratedSlot
import PlanarUnitDistances.RecordSlot

namespace OAI.PlanarUnitDistances.PhysicalLevels
open Set Finset MeasureTheory FiniteLaw FiniteStarCoupling CommonTemplate StarScore
open _root_.PlanarUnitDistances.Flanks _root_.PlanarUnitDistances.ComparisonConstants
open scoped Classical
noncomputable section
variable {P Q I : Type*} [Fintype P] [Fintype Q] [Fintype I]

theorem frequency_threshold {T : Type*} [Fintype T] (μ : Law T) (Z : T → ℝ) (s : ℝ) :
    frequency μ (fun t => decide (s<Z t))=thresholdTail μ.val Z s := by
  unfold frequency thresholdTail event avg
  apply Finset.sum_congr rfl; intro t _
  by_cases h : s<Z t <;> simp [h]

theorem base_slot_at_place (π : Law (P×Q)) (μ : Law I) (edge : I → P×Q)
    (base : P⊕Q) (neighbor : I → P⊕Q)
    (label : Record P Q → Finset (P⊕Q)×Finset (P⊕Q))
    (R : ℝ → Record P Q) (Z : I → ℝ) (lo hi : ℝ) (f : ℝ → ℝ)
    (one : ∀s,event π (fun e => (R s).bit e.1 e.2=true)=f s)
    (bits : ∀s i,(R s).bit (edge i).1 (edge i).2=decide (s<Z i))
    (i j : I) (iwin : Z i∈Icc lo hi) (jwin : Z j∈Icc lo hi) :
    let r := fun s => decide (f s≤1/2)
    let x := fun s => vertexState (R s) base
    let Y := fun s i => vertexState (R s) (neighbor i)
    let keep := fun s => good π (R s) ∧ RareScore.exceptional (r s) (label (R s)) (x s)
    let z := fun s => (Y s i).1=(Y s j).1
    let w := fun s => (Y s i).2=(Y s j).2
    let F := positive lo hi (dy 1800) (Z i) (Z j) f (thresholdTail μ.val Z) z w keep
    Integrable F → (∫s in Icc lo hi,baseSlot π μ edge base neighbor label i j (R s)) =
      (∫s,F s)-|Z i-Z j| := by
  intro r x Y keep z w F integrable
  have half : dy 1800≤1/2 := by
    exact (antitone (by decide : 1≤1800)).trans_eq (by norm_num [dy])
  have point (s : ℝ) :
      baseSlot π μ edge base neighbor label i j (R s) =
        observedSlot (dy 1800 ≤ min (f s) (1-f s)) (good π (R s)) (r s) (label (R s))
          (x s) (thresholdTail μ.val Z s) (fun k => decide (s<Z k)) (Y s) i j := by
    have bitEq : (fun i => (R s).bit (edge i).1 (edge i).2)=(fun i => decide (s<Z i)) := funext (bits s)
    simp only [baseSlot,common,minority,rareBit,one s,bitEq,frequency_threshold]
    rfl
  rw [setIntegral_congr_fun measurableSet_Icc (fun s _ => point s)]
  exact integrated_observedSlot lo hi (dy 1800) half f (thresholdTail μ.val Z) (fun s => good π (R s))
    (fun s => label (R s)) x Y Z i j iwin jwin integrable

end
end OAI.PlanarUnitDistances.PhysicalLevels
