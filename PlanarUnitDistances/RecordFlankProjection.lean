import PlanarUnitDistances.FixedBaseSlot
import PlanarUnitDistances.PhysicalFlankGeometry

namespace OAI.PlanarUnitDistances.PhysicalLevels
open Set Finset MeasureTheory NumberField FiniteLaw FiniteStarCoupling CommonTemplate StarScore
open _root_.PlanarUnitDistances.Flanks _root_.PlanarUnitDistances.ComparisonConstants
open Real (log exp exp_log exp_zero)
open scoped Classical
noncomputable section
variable {P Q I K : Type*} [Fintype P] [Fintype Q] [Fintype I] [Field K] [NumberField K]

/-- Identifications checked on the actual record at one value of the
place. They compare only single bits, label equalities and the choice of
the retained rare event, before taking any paired average or integral. -/
structure PlaceIdentification (π : Law (P×Q)) (μ : Law I) (edge : I → P×Q)
    (base : P⊕Q) (neighbor : I → P⊕Q)
    (label : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)) (R : ℝ → Record P Q)
    (d : I → K) (v : AbsoluteValue K ℝ) (c : ℝ) (L : LocalComparison μ.val d v (dy 1800) c) : Prop where
  frequency : ∀s,event π (fun e => (R s).bit e.1 e.2=true)=L.globalTail s
  bit : ∀s i,(R s).bit (edge i).1 (edge i).2=decide (s<BudgetPlaces.threshold v (d i))
  direct : ∀i j s,(vertexState (R s) (neighbor i)).1=(vertexState (R s) (neighbor j)).1 ↔ L.direct i j s
  reciprocal : ∀i j s,(vertexState (R s) (neighbor i)).2=(vertexState (R s) (neighbor j)).2 ↔ L.reciprocal i j s
  keep : ∀i j s,(good π (R s) ∧ RareScore.exceptional (rareBit π (R s)) (label (R s)) (vertexState (R s) base)) ↔
    L.keep i j s
  window : ∀i,BudgetPlaces.threshold v (d i)∈Icc L.lo L.hi

namespace PlaceIdentification
variable {π : Law (P×Q)} {μ : Law I} {edge : I → P×Q} {base : P⊕Q} {neighbor : I → P⊕Q}
  {label : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)} {R : ℝ → Record P Q}
  {d : I → K} {v : AbsoluteValue K ℝ} {c : ℝ} {L : LocalComparison μ.val d v (dy 1800) c}

theorem integral_slot (A : PlaceIdentification π μ edge base neighbor label R d v c L)
    (i j : I) (hne : i≠j) :
    (∫s in Icc L.lo L.hi,baseSlot π μ edge base neighbor label i j (R s))=L.pairScore i j := by
  have za : (fun s => (vertexState (R s) (neighbor i)).1=(vertexState (R s) (neighbor j)).1)=L.direct i j :=
    funext (fun s => propext (A.direct i j s))
  have wa : (fun s => (vertexState (R s) (neighbor i)).2=(vertexState (R s) (neighbor j)).2)=L.reciprocal i j :=
    funext (fun s => propext (A.reciprocal i j s))
  have kk : (fun s => good π (R s) ∧ RareScore.exceptional (decide (L.globalTail s≤1/2))
      (label (R s)) (vertexState (R s) base))=L.keep i j := by
    funext s
    rw [←A.frequency s]
    exact propext (A.keep i j s)
  have eq := base_slot_at_place π μ edge base neighbor label R (BudgetPlaces.threshold v ∘ d)
    L.lo L.hi L.globalTail A.frequency A.bit i j (A.window i) (A.window j)
  dsimp only at eq
  rw [za,wa,kk] at eq
  exact eq (L.integrable i j hne)

theorem integral_variation (A : PlaceIdentification π μ edge base neighbor label R d v c L) :
    (∫s in Icc L.lo L.hi, if common π (R s) then variation μ
      (fun i => (R s).bit (edge i).1 (edge i).2) else 0)=L.comparison := by
  let Z := BudgetPlaces.threshold v ∘ d
  let g := thresholdTail μ.val Z
  let C := commonRegion L.lo L.hi (dy 1800) L.globalTail
  have cm : MeasurableSet C := measurableSet_Icc.inter
    ((measurableSet_le measurable_const L.antitone.measurable).inter
      (measurableSet_le L.antitone.measurable measurable_const))
  have included : C⊆Icc L.lo L.hi := fun _ h => h.1
  have common_iff (s : ℝ) (hs : s∈Icc L.lo L.hi) :
      common π (R s) ↔ s∈C := by
    change dy 1800 ≤ min (event π (fun e => (R s).bit e.1 e.2=true)) _ ↔ _
    rw [A.frequency s,le_min_iff]
    change _ ↔ s∈Icc L.lo L.hi ∧ dy 1800≤L.globalTail s ∧ L.globalTail s≤1-dy 1800
    constructor
    · intro h; exact ⟨hs,h.1,by linarith [h.2]⟩
    · intro h; exact ⟨h.2.1,by linarith [h.2.2]⟩
  calc
    _ = ∫s in Icc L.lo L.hi,C.indicator (fun t => 2*g t*(1-g t)) s := by
      apply setIntegral_congr_fun measurableSet_Icc; intro s hs
      have eq : (fun i => (R s).bit (edge i).1 (edge i).2)=(fun i => decide (s<Z i)) := funext (A.bit s)
      by_cases inC : s∈C <;> simp [Set.indicator,inC,common_iff s hs,eq,variation,frequency_threshold,g]
    _ = _ := by
      rw [integral_indicator cm,Measure.restrict_restrict cm,Set.inter_eq_left.mpr included]
      rfl

end PlaceIdentification
end
end OAI.PlanarUnitDistances.PhysicalLevels
