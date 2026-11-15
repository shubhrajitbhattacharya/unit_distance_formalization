import PlanarUnitDistances.RecordBaseUpper
import PlanarUnitDistances.UniformPhysical

namespace PlanarUnitDistances.UniformPhysical
open Set MeasureTheory NumberField Finset OAI.PlanarUnitDistances Flanks ComparisonConstants
open FiniteLaw CommonTemplate PhysicalLabels PhysicalLevels StarScore UniformNormalization EdgeHeightScale
open Real (log exp exp_log exp_zero)
open scoped Classical
noncomputable section
variable {P Q I K : Type} [Fintype P] [Fintype Q] [Fintype I] [Field K] [NumberField K]

private def edgeThreshold (v : AbsoluteValue K ℝ) (z : P⊕Q → K) (e : P×Q) :=
  -log (v (z (.inl e.1)-z (.inr e.2)))

private theorem vertex_arch (v : InfinitePlace K) (az aw : ℝ×ℝ) (z w : P⊕Q → K) (t : ℝ) (x : P⊕Q) :
    vertexState (arch v az aw z w t) x=archPair v az aw z w t x := by cases x <;> rfl

private theorem vertex_fin (v : FinitePlace K) (z w : P⊕Q → K) (t : ℝ) (x : P⊕Q) :
    vertexState (PhysicalLevels.finite v z w t) x=finitePair v z w t x := by cases x <;> rfl

/-- The upper bound for a fixed point, center, or point/list base on the
original physical graph and its profile windows. The edges in the support
of its conditional law may be presented in either orientation. -/
theorem graph_base_upper (rows : Q → Finset P) (z w : P⊕Q → K)
    (π : Law (P×Q)) (μ : Law I) (edge : I → P×Q) (base : P⊕Q) (neighbor : I → P⊕Q)
    (label : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)) (az aw : InfinitePlace K → ℝ×ℝ)
    (support : ∀i,(edge i).1∈rows (edge i).2)
    (ends : ∀i,(neighbor i=.inl (edge i).1 ∧ base=.inr (edge i).2) ∨
      (neighbor i=.inr (edge i).2 ∧ base=.inl (edge i).1))
    (inj : Function.Injective (z ∘ neighbor))
    (unit : ∀i,(z (neighbor i)-z base)*(w (neighbor i)-w base)=1) :
    let ν := fullMeasure rows z w az aw
    offAvg μ.val (fun q => ∫t,baseSlot π μ edge base neighbor label q.1 q.2 t ∂ν) ≤
      (∫t,variation μ (fun i => t.bit (edge i).1 (edge i).2) ∂commonLaw π ν)/15+2*log 2 := by
  let d := neighborDirection (z base) (z ∘ neighbor)
  have nonzero (i : I) : d i ≠ 0 := left_ne_zero_of_mul_eq_one (unit i)
  have di : Function.Injective d := fun _ _ h => inj (sub_left_inj.mp h)
  let rad := profileRadius rows z w
  have direction_eq (v : AbsoluteValue K ℝ) (i : I) :
      v (z (.inl (edge i).1)-z (.inr (edge i).2))=v (d i) := by
    rcases ends i with ⟨n,b⟩|⟨n,b⟩
    · simp only [d,neighborDirection,Function.comp_apply,n,b]
    · simp only [d,neighborDirection,Function.comp_apply,n,b]
      rw [←neg_sub (z (.inl _)) (z (.inr _)),v.map_neg]
  have threshold_eq (v : AbsoluteValue K ℝ) (i : I) : edgeThreshold v z (edge i)=BudgetPlaces.threshold v (d i) := by
    simp only [edgeThreshold,BudgetPlaces.threshold,direction_eq]
  have win (v : AbsoluteValue K ℝ) (i : I) :
      BudgetPlaces.threshold v (d i) ∈ Icc (-rad v) (rad v) := by
    have h := (radius_bounds rows z w v).1 (edge i)
    change -profileRadius rows z w v ≤ -log (v (d i)) ∧ -log (v (d i)) ≤ profileRadius rows z w v
    simpa only [EdgeHeightScale.threshold,UniformNormalization.direction,if_pos (support i),direction_eq] using
      (abs_le.mp h)
  have outside (v : FinitePlace K) (hv : v∉primes rows z w) (i : I) : v (d i)=1 := by
    obtain ⟨l,h⟩ := win v.1 i
    have zero : rad v.1=0 := radius_zero rows z w hv
    have logZero : log (v.1 (d i))=0 := by
      change -rad v.1 ≤ -log (v.1 (d i)) at l
      change -log (v.1 (d i)) ≤ rad v.1 at h
      linarith only [l,h,zero]
    change v.1 (d i)=1
    have e := congrArg exp logZero
    simpa only [exp_log (v.1.pos (nonzero i)),exp_zero] using e
  let f (v : AbsoluteValue K ℝ) := thresholdTail π.val (edgeThreshold v z)
  let keep (R : ℝ → Record P Q) (_ _ : I) (s : ℝ) :=
    good π (R s) ∧ RareScore.exceptional (rareBit π (R s)) (label (R s)) (vertexState (R s) base)
  have meas (R : ℝ → Record P Q) (h : Measurable R) (i j : I) : MeasurableSet {s | keep R i j s} :=
    (Set.toFinite {r : Record P Q | good π r ∧ RareScore.exceptional (rareBit π r) (label r) (vertexState r base)}).measurableSet.preimage h
  let ia (v : InfinitePlace K) := arch v (az v) (aw v) z w
  let fp (v : FinitePlace K) := PhysicalLevels.finite v z w
  let A (v : InfinitePlace K) := archGeometry μ.val (b:=z base) (u:=w base) (z ∘ neighbor) (w ∘ neighbor)
    inj unit v (az v) (aw v) (-rad v.1) (rad v.1) (dy 1800) (f v.1) (tail_antitone _ _ π.nonneg)
    (keep (ia v)) (meas _ (measurable_arch ..))
  let B (v : FinitePlace K) := finiteGeometry μ.val (b:=z base) (u:=w base) (z ∘ neighbor) (w ∘ neighbor)
    inj unit v (-rad v.1) (rad v.1) (dy 1800) (f v.1) (tail_antitone _ _ π.nonneg)
    (keep (fp v)) (meas _ (measurable_finite ..))
  have aID (v : InfinitePlace K) : PlaceIdentification π μ edge base neighbor label (ia v) d v.1 (log 2) (A v) := by
    constructor
    · exact fun s => frequency_threshold π (edgeThreshold v.1 z) s
    · intro s i
      change decide (s<edgeThreshold v.1 z (edge i))=_
      rw [threshold_eq]
    · intro i j s
      rw [vertex_arch,vertex_arch]
      exact archLabel_eq v (az v) z (-s) _ _
    · intro i j s
      rw [vertex_arch,vertex_arch]
      exact archLabel_eq v (aw v) w s _ _
    · exact fun _ _ _ => Iff.rfl
    · exact win v.1
  have bID (v : FinitePlace K) : PlaceIdentification π μ edge base neighbor label (fp v) d v.1 0 (B v) := by
    constructor
    · exact fun s => frequency_threshold π (edgeThreshold v.1 z) s
    · intro s i
      change decide (s<edgeThreshold v.1 z (edge i))=_
      rw [threshold_eq]
    · intro i j s
      rw [vertex_fin,vertex_fin]
      exact finiteLabel_eq v z (-s) _ _
    · intro i j s
      rw [vertex_fin,vertex_fin]
      exact finiteLabel_eq v w s _ _
    · exact fun _ _ _ => Iff.rfl
    · exact win v.1
  exact record_base_upper π μ edge base neighbor label z w az aw (primes rows z w) d nonzero di outside A B aID bID

end
end PlanarUnitDistances.UniformPhysical
