import PlanarUnitDistances.RecordSlot
import PlanarUnitDistances.RecordScorePartition
import PlanarUnitDistances.PositiveAtoms

namespace OAI.PlanarUnitDistances.PhysicalLevels
open MeasureTheory FiniteLaw StarScore FiniteStarCoupling TemplateCoupling RareScore
open _root_.PlanarUnitDistances.Flanks Finset
open scoped Classical
noncomputable section
variable {P Q I T : Type*} [Fintype P] [Fintype Q] [Fintype I] [Fintype T]

/-- Averaging a slot at a fixed base uses the bias of its own neighbor law.
Only the classification of the level uses the full original edge law. -/
theorem pair_baseSlot (π : Law (P×Q)) (μ : Law I) (edge : I → P×Q) (b : P⊕Q)
    (neighbors : I → P⊕Q) (l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)) (t : Record P Q) :
    let bits := fun i => t.bit (edge i).1 (edge i).2
    let states := fun i => vertexState t (neighbors i)
    avg (pair μ μ) (fun ij => baseSlot π μ edge b neighbors l ij.1 ij.2 t) =
      levelScore π t (score μ bits states)
        (avg (pair μ μ) (fun ij => RareScore.slot (rareBit π t) (l t)
          (vertexState t b) (states ij.1) (states ij.2) (bits ij.1) (bits ij.2)))
        (variation μ bits) := by
  dsimp only
  by_cases hc : common π t
  · simp only [baseSlot,observedSlot,levelScore,hc,if_true,score]
  · by_cases hg : good π t
    · simp only [baseSlot,observedSlot,levelScore,hc,hg,if_false,if_true]
    · simp only [baseSlot,observedSlot,levelScore,hc,hg,if_false,← StarScore.mismatch]
      simp [avg,event,RareScore.ind,Finset.sum_neg_distrib]

theorem center_baseSlots (π ρ : Law (P×Q)) (l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q))
    (t : Record P Q) :
    avg (right ρ) (fun q => avg (pair (col ρ q) (col ρ q)) (fun pr =>
        baseSlot π (col ρ q) (fun p => (p,q)) (.inr q) Sum.inl l pr.1 pr.2 t)) =
      levelScore π t (DQ ρ t.bit t.x) (centerScore ρ (rareBit π t) (l t) t.x t.y t.bit)
        (VQ ρ t.bit) := by
  simp_rw [pair_baseSlot]
  exact avg_levelScore π t (right ρ) _ _ _

theorem point_baseSlots (π ρ : Law (P×Q)) (l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q))
    (t : Record P Q) :
    avg (left ρ) (fun p => avg (pair (row ρ p) (row ρ p)) (fun qr =>
        baseSlot π (row ρ p) (fun q => (p,q)) (.inl p) Sum.inr l qr.1 qr.2 t)) =
      levelScore π t (DP ρ t.bit t.y) (pointScore ρ (rareBit π t) (l t) t.x t.y t.bit)
        (VP ρ t.bit) := by
  simp_rw [pair_baseSlot]
  exact avg_levelScore π t (left ρ) _ _ _

theorem center_integrated_slots (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν]
    (l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)) :
    (∫t, DQ π t.bit t.x ∂commonLaw π ν) +
      rareIntegral π ν (fun t => centerScore π (rareBit π t) (l t) t.x t.y t.bit) (fun t => VQ π t.bit) =
    avg (right π) (fun q => avg (pair (col π q) (col π q)) (fun pr =>
      ∫t, baseSlot π (col π q) (fun p => (p,q)) (.inr q) Sum.inl l pr.1 pr.2 t ∂ν)) := by
  rw [← integral_levelScore]
  simp_rw [← center_baseSlots π π l]
  rw [FiniteLawIntegral.integral_avg _ _ (fun _ => Integrable.of_finite)]
  apply avg_congr; intro q
  exact FiniteLawIntegral.integral_avg _ _ (fun _ => Integrable.of_finite)

theorem point_integrated_slots (π ρ : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν]
    (l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)) :
    (∫t, DP ρ t.bit t.y ∂commonLaw π ν) +
      rareIntegral π ν (fun t => pointScore ρ (rareBit π t) (l t) t.x t.y t.bit) (fun t => VP ρ t.bit) =
    avg (left ρ) (fun p => avg (pair (row ρ p) (row ρ p)) (fun qr =>
      ∫t, baseSlot π (row ρ p) (fun q => (p,q)) (.inl p) Sum.inr l qr.1 qr.2 t ∂ν)) := by
  rw [← integral_levelScore]
  simp_rw [← point_baseSlots π ρ l]
  rw [FiniteLawIntegral.integral_avg _ _ (fun _ => Integrable.of_finite)]
  apply avg_congr; intro p
  exact FiniteLawIntegral.integral_avg _ _ (fun _ => Integrable.of_finite)

theorem list_integrated_slots (π : Law (P×Q)) (a : Q → Law T)
    (ν : Measure (Record P Q)) [IsFiniteMeasure ν] (l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)) :
    (∫t, avg (templates π a) (fun u => DP (slice π a u) t.bit t.y) ∂commonLaw π ν) +
      rareIntegral π ν (fun t => avg (templates π a) (fun u =>
        pointScore (slice π a u) (rareBit π t) (l t) t.x t.y t.bit))
        (fun t => avg (templates π a) (fun u => VP (slice π a u) t.bit)) =
    avg (templates π a) (fun u => let ρ := slice π a u
      avg (left ρ) (fun p => avg (pair (row ρ p) (row ρ p)) (fun qr =>
        ∫t, baseSlot π (row ρ p) (fun q => (p,q)) (.inl p) Sum.inr l qr.1 qr.2 t ∂ν))) := by
  rw [← integral_levelScore]
  simp_rw [← avg_levelScore]
  rw [FiniteLawIntegral.integral_avg _ _ (fun _ => Integrable.of_finite)]
  apply avg_congr; intro u
  rw [integral_levelScore]
  exact point_integrated_slots π (slice π a u) ν l

end
end OAI.PlanarUnitDistances.PhysicalLevels
