import PlanarUnitDistances.PosteriorPlaces

namespace OAI.PlanarUnitDistances.PhysicalLabels
open Finset MeasureTheory Set Real NumberField GridShift StateConsistency PosteriorPlaces
open scoped Classical
noncomputable section
variable {V Ω : Type*} [Fintype V] [MeasurableSpace Ω]

/-- The set of vertices belonging to the given vertex's cell is itself a
canonical finite label. Both sides of the bipartition use the same vertex set. -/
def label (R : Ω → V → V → Prop) (s : Ω) (x : V) : Finset V :=
  univ.filter (R s x)

lemma measurable_label (R : Ω → V → V → Prop)
    (hm : ∀ x y, MeasurableSet {s | R s x y}) (x : V) :
    Measurable (fun s => label R s x) := by
  apply measurable_finset_iff.mpr
  intro y
  apply measurableSet_setOf.mp
  simpa [label] using hm x y

omit [MeasurableSpace Ω] in
lemma label_eq_iff (R : Ω → V → V → Prop) (s : Ω) (hr : Equivalence (R s)) (x y : V) :
    label R s x=label R s y ↔ R s x y := by
  constructor
  · intro hh
    have hy : y ∈ label R s y := mem_filter.mpr ⟨mem_univ _,hr.refl _⟩
    exact (mem_filter.mp (hh ▸ hy : y ∈ label R s x)).2
  · intro hh
    ext z
    simp only [label,mem_filter,Finset.mem_univ,true_and]
    exact ⟨hr.trans (hr.symm hh),hr.trans hh⟩

variable {K : Type*} [Field K] [NumberField K]
def archLabel (v : InfinitePlace K) (u : ℝ×ℝ) (z : V → K) (s : ℝ) (x : V) :=
  label (fun t x y => archMatch v u (z x) (z y) t) s x

def finiteLabel (v : FinitePlace K) (z : V → K) (s : ℝ) (x : V) :=
  label (fun t x y => finiteMatch v (z x) (z y) t) s x

omit [NumberField K] in
theorem archLabel_eq (v : InfinitePlace K) (u : ℝ×ℝ) (z : V → K) (s : ℝ) (x y : V) :
    archLabel v u z s x = archLabel v u z s y ↔ archMatch v u (z x) (z y) s := by
  apply label_eq_iff
  exact ⟨fun _ => rfl, fun hh => Eq.symm hh, fun h₁ h₂ => Eq.trans h₁ h₂⟩

lemma nonarch (v : FinitePlace K) : IsNonarchimedean v.1 := by
  intro x y
  change v (x+y) ≤ max (v x) (v y)
  simp_rw [←v.norm_embedding_eq,FinitePlace.norm_embedding]
  exact NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K (v.maximalIdeal) x y

theorem finiteLabel_eq (v : FinitePlace K) (z : V → K) (s : ℝ) (x y : V) :
    finiteLabel v z s x = finiteLabel v z s y ↔ finiteMatch v (z x) (z y) s := by
  exact label_eq_iff _ _ ⟨fun x => (localSetoid v.1 (nonarch v) s).refl (z x),
    fun h => (localSetoid v.1 (nonarch v) s).symm h,fun h₁ h₂ => (localSetoid v.1 (nonarch v) s).trans h₁ h₂⟩ _ _

omit [NumberField K] in
theorem measurable_archLabel (v : InfinitePlace K) (u : ℝ×ℝ) (z : V → K) (x : V) :
    Measurable (fun s => archLabel v u z s x) :=
  measurable_label _ (fun x y => arch_meas v u (z x) (z y) id measurable_id) x

theorem measurable_finiteLabel (v : FinitePlace K) (z : V → K) (x : V) :
    Measurable (fun s => finiteLabel v z s x) :=
  measurable_label _ (fun _ _ => measurableSet_le measurable_const measurable_exp) x

/-- One point/center pair of labels gives the same score as the original
grid or ball comparisons. Both maps are measurable on the continuum of levels. -/
def archPair (v : InfinitePlace K) (u₁ u₂ : ℝ×ℝ) (z w : V → K) (s : ℝ) (x : V) :=
  (archLabel v u₁ z (-s) x, archLabel v u₂ w s x)
def finitePair (v : FinitePlace K) (z w : V → K) (s : ℝ) (x : V) :=
  (finiteLabel v z (-s) x, finiteLabel v w s x)

omit [NumberField K] in
theorem measurable_archPair (v : InfinitePlace K) (u₁ u₂ : ℝ×ℝ) (z w : V → K) (x : V) :
    Measurable (fun s => archPair v u₁ u₂ z w s x) :=
  ((measurable_archLabel v u₁ z x).comp measurable_neg).prodMk (measurable_archLabel v u₂ w x)

theorem measurable_finitePair (v : FinitePlace K) (z w : V → K) (x : V) :
    Measurable (fun s => finitePair v z w s x) :=
  ((measurable_finiteLabel v z x).comp measurable_neg).prodMk (measurable_finiteLabel v w x)

omit [NumberField K] in
lemma arch_score (v : InfinitePlace K) (u₁ u₂ : ℝ×ℝ) (z w : V → K) (s : ℝ) (x y : V) :
    PredictionCut.pairScore (archPair v u₁ u₂ z w s x) (archPair v u₁ u₂ z w s y) =
    score (fun t => archMatch v u₁ (z x) (z y) (-t)) (archMatch v u₂ (w x) (w y)) s := by
  simp only [PredictionCut.pairScore,archPair,score,archLabel_eq]

lemma finite_score (v : FinitePlace K) (z w : V → K) (s : ℝ) (x y : V) :
    PredictionCut.pairScore (finitePair v z w s x) (finitePair v z w s y) =
    score (fun t => finiteMatch v (z x) (z y) (-t)) (finiteMatch v (w x) (w y)) s := by
  simp only [PredictionCut.pairScore,finitePair,score,finiteLabel_eq]

/-- The actual finitely encoded labels satisfy the off-diagonal bound needed
by the posterior cutoff theorem for these physical level intervals. -/
theorem all_labels (z w : V → K) (x y : V) (hz : z x ≠ z y) (hw : w x ≠ w y)
    (F : Finset (FinitePlace K))
    (hsupp : ∀ v : FinitePlace K, v ∉ F → v ((z x-z y)*(w x-w y))=1)
    (U V' : InfinitePlace K → ℝ×ℝ) (l r : InfinitePlace K → ℝ) (l' r' : FinitePlace K → ℝ)
    (ord : ∀v,l v≤r v) (lo : ∀v,l v≤-log (v (z x-z y))) (hi : ∀v,log (v (w x-w y))≤r v)
    (ord' : ∀v∈F,l' v≤r' v) (lo' : ∀v∈F,l' v≤-log (v (z x-z y))) (hi' : ∀v∈F,log (v (w x-w y))≤r' v) :
    ((∑ v : InfinitePlace K, (v.mult:ℝ)*(∫s in Icc (l v) (r v),
      PredictionCut.pairScore (archPair v (U v) (V' v) z w s x) (archPair v (U v) (V' v) z w s y)))+
      ∑ v∈F, ∫s in Icc (l' v) (r' v),
      PredictionCut.pairScore (finitePair v z w s x) (finitePair v z w s y))/(Module.finrank ℚ K:ℝ) ≤ log 2 := by
  simpa only [arch_score,finite_score] using all_places hz hw F hsupp U V' l r l' r' ord lo hi ord' lo' hi'

end
end OAI.PlanarUnitDistances.PhysicalLabels
