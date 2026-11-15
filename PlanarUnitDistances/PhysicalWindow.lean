import PlanarUnitDistances.ArithmeticLevels

namespace PlanarUnitDistances.Competition.IncidencePiece
open Finset MeasureTheory NumberField Real Set
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

def frequencyMinority (M : IncidencePiece K) (v : K → ℝ) (s : ℝ) : ℝ :=
  let h := M.edgeProb (fun e => s<M.threshold v e); min h (1-h)

private lemma above (M : IncidencePiece K) (v : K → ℝ) (s : ℝ)
    (hl : ∀e∈M.E,M.threshold v e≤s) : M.frequencyMinority v s=0 := by
  have eq : M.E.filter (fun e => s<M.threshold v e)=∅ :=
    eq_empty_iff_forall_notMem.mpr fun e hm => (not_lt_of_ge (hl _ (mem_filter.mp hm).1)) (mem_filter.mp hm).2
  simp [frequencyMinority,edgeProb,eq]

private lemma below (M : IncidencePiece K) (he : 0<(M.E.card:ℝ)) (v : K → ℝ) (s : ℝ)
    (hu : ∀e∈M.E,s<M.threshold v e) : M.frequencyMinority v s=0 := by
  have eq : M.E.filter (fun e => s<M.threshold v e)=M.E := filter_eq_self.mpr hu
  simp [frequencyMinority,edgeProb,eq,div_self he.ne']

theorem window_width (M : IncidencePiece K) (he : 0<(M.E.card:ℝ)) (v : K → ℝ) (l h : ℝ)
    (lo : ∀e∈M.E,l≤M.threshold v e) (hi : ∀e∈M.E,M.threshold v e≤h) :
    (∫s in Icc l h,M.frequencyMinority v s)=M.localWidth v := by
  rw [←integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  change (Icc l h).indicator (M.frequencyMinority v) s=M.frequencyMinority v s
  by_cases hs : s∈Icc l h
  · exact indicator_of_mem hs _
  rw [indicator_of_notMem hs]
  by_cases h1 : s<l
  · exact (below M he v s (fun e he => h1.trans_le (lo e he))).symm
  · have h2 : h<s := lt_of_not_ge (fun he => hs ⟨le_of_not_gt h1,he⟩)
    exact (above M v s (fun e he => (hi e he).trans h2.le)).symm


theorem width_zero (M : IncidencePiece K) (he : 0<(M.E.card:ℝ)) (v : K → ℝ)
    (hz : ∀e∈M.E,M.threshold v e=0) : M.localWidth v=0 := by
  rw [←window_width M he v 0 0 (fun e he => (hz e he).ge) (fun e he => (hz e he).le)]
  simp

end
end PlanarUnitDistances.Competition.IncidencePiece
