import PlanarUnitDistances.PhysicalLabels
import PlanarUnitDistances.IntegratedScores

namespace OAI.PlanarUnitDistances.PhysicalLevels
open Finset Set MeasureTheory NumberField CommonTemplate PhysicalLabels
open scoped Classical NNReal
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q] {K : Type*} [Field K] [NumberField K]

abbrev Record (P Q : Type*) := CommonLevel P Q (Finset (P⊕Q)) (Finset (P⊕Q))

def make (states : P⊕Q → Finset (P⊕Q) × Finset (P⊕Q)) (b : P → Q → Bool) : Record P Q :=
  ⟨fun p => states (.inl p),fun q => states (.inr q),b⟩

def arch (v : InfinitePlace K) (U V : ℝ×ℝ) (z w : P⊕Q → K) (s : ℝ) : Record P Q :=
  make (archPair v U V z w s) (fun p q => decide (s < -Real.log (v (z (.inl p)-z (.inr q)))))
def finite (v : FinitePlace K) (z w : P⊕Q → K) (s : ℝ) : Record P Q :=
  make (finitePair v z w s) (fun p q => decide (s < -Real.log (v (z (.inl p)-z (.inr q)))))

private lemma measurable_bit (b : ℝ) : Measurable (fun s => decide (s<b)) := by
  have he : (fun s : ℝ => decide (s<b)) = (fun s => if s<b then true else false) := by
    funext s; by_cases h : s<b <;> simp [h]
  rw [he]
  apply Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const

omit [NumberField K] in
lemma measurable_arch (v : InfinitePlace K) (U V : ℝ×ℝ) (z w : P⊕Q → K) :
    Measurable (arch v U V z w) :=
  measurable_snapshot _ (fun p => measurable_archPair v U V z w (.inl p))
    (fun q => measurable_archPair v U V z w (.inr q)) (fun _ _ => measurable_bit _)

lemma measurable_finite (v : FinitePlace K) (z w : P⊕Q → K) : Measurable (finite v z w) :=
  measurable_snapshot _ (fun p => measurable_finitePair v z w (.inl p))
    (fun q => measurable_finitePair v z w (.inr q)) (fun _ _ => measurable_bit _)

variable {T : Type*} [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]

def intervalRecord (t : ℝ → T) (l r : ℝ) : Measure T := (volume.restrict (Icc l r)).map t
instance (t : ℝ → T) (l r : ℝ) : IsFiniteMeasure (intervalRecord t l r) := by
  unfold intervalRecord; infer_instance

def degreeWeight (K : Type*) [Field K] [NumberField K] : ℝ≥0 :=
  ⟨(Module.finrank ℚ K:ℝ)⁻¹,inv_nonneg.mpr (Nat.cast_nonneg _)⟩

/-- A measure on the finite record alphabet, obtained by transporting ordinary
Lebesgue measure on each place interval with the product-formula weights. -/
def measure (F : Finset (FinitePlace K)) (z w : P⊕Q → K) (U V : InfinitePlace K → ℝ×ℝ)
    (l r : InfinitePlace K → ℝ) (l' r' : FinitePlace K → ℝ) : Measure (Record P Q) :=
  degreeWeight K • ((∑ v : InfinitePlace K, (v.mult:ℝ≥0) • intervalRecord (arch v (U v) (V v) z w) (l v) (r v))+
    ∑ v∈F, intervalRecord (finite v z w) (l' v) (r' v))

instance (F : Finset (FinitePlace K)) (z w : P⊕Q → K) (U V : InfinitePlace K → ℝ×ℝ)
    (l r : InfinitePlace K → ℝ) (l' r' : FinitePlace K → ℝ) :
    IsFiniteMeasure (measure F z w U V l r l' r') := by unfold measure; infer_instance

lemma record_integral (t : ℝ → T) (ht : Measurable t) (l r : ℝ) (f : T → ℝ) :
    (∫j, f j ∂intervalRecord t l r)=∫s in Icc l r, f (t s) := by
  rw [intervalRecord,integral_map ht.aemeasurable (measurable_of_finite f).aestronglyMeasurable]

/-- The finite record law preserves the original continuum integral of every
statistic of the recorded labels and bits, including later history-dependent tests. -/
theorem integral_measure (F : Finset (FinitePlace K)) (z w : P⊕Q → K) (U V : InfinitePlace K → ℝ×ℝ)
    (l r : InfinitePlace K → ℝ) (l' r' : FinitePlace K → ℝ) (f : Record P Q → ℝ) :
    (∫j, f j ∂measure F z w U V l r l' r') =
    ((∑ v : InfinitePlace K, (v.mult:ℝ)*(∫s in Icc (l v) (r v), f (arch v (U v) (V v) z w s)))+
      ∑v∈F,∫s in Icc (l' v) (r' v), f (finite v z w s))/(Module.finrank ℚ K:ℝ) := by
  unfold measure
  rw [integral_smul_nnreal_measure,integral_add_measure Integrable.of_finite Integrable.of_finite,
    integral_finsetSum_measure (fun _ _ => Integrable.of_finite),integral_finsetSum_measure (fun _ _ => Integrable.of_finite)]
  simp only [integral_smul_nnreal_measure,NNReal.smul_def,smul_eq_mul,NNReal.coe_natCast,degreeWeight]
  simp_rw [record_integral _ (measurable_arch ..),record_integral _ (measurable_finite ..)]
  change (Module.finrank ℚ K:ℝ)⁻¹ * _ = _
  ring

/-- The global off-diagonal estimate on exactly the record law used for the
common-score comparisons and all exceptional-width integrals. -/
theorem posterior_pair_bound (F : Finset (FinitePlace K)) (z w : P⊕Q → K)
    (U V : InfinitePlace K → ℝ×ℝ) (l r : InfinitePlace K → ℝ) (l' r' : FinitePlace K → ℝ) {p p' : P}
    (h₁ : z (.inl p)≠z (.inl p')) (h₂ : w (.inl p)≠w (.inl p'))
    (hsupp : ∀ v : FinitePlace K, v ∉ F → v ((z (.inl p)-z (.inl p'))*(w (.inl p)-w (.inl p')))=1)
    (ord : ∀v,l v≤r v) (lo : ∀v,l v≤-Real.log (v (z (.inl p)-z (.inl p'))))
    (hi : ∀v,Real.log (v (w (.inl p)-w (.inl p')))≤r v)
    (ord' : ∀v∈F,l' v≤r' v) (lo' : ∀v∈F,l' v≤-Real.log (v (z (.inl p)-z (.inl p'))))
    (hi' : ∀v∈F,Real.log (v (w (.inl p)-w (.inl p')))≤r' v) :
    (∫j, PredictionCut.pairScore (j.x p) (j.x p') ∂measure F z w U V l r l' r') ≤ Real.log 2 := by
  rw [integral_measure]
  exact all_labels z w (.inl p) (.inl p') h₁ h₂ F hsupp U V l r l' r' ord lo hi ord' lo' hi'

end
end OAI.PlanarUnitDistances.PhysicalLevels
