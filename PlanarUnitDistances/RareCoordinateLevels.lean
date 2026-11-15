import PlanarUnitDistances.RareLabels

namespace PlanarUnitDistances.Competition.IncidencePiece
open Finset MeasureTheory
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K] {L : Type*} [Fintype L] [Nonempty L]

/-- A record of both coordinate partitions and the edge threshold bits at a
place and level. Both ends of each edge use the same plane labeling. -/
structure CoordinateLevel (L : Type*) where
  label : Plane → L×L
  bit : Plane×Plane → Bool
  majority : Bool

def CoordinateLevel.selected (r : CoordinateLevel L) (p : Plane) :=
  if r.majority then (r.label p).1 else (r.label p).2

def CoordinateLevel.consistent (r : CoordinateLevel L) (e : Plane×Plane) : Prop :=
  if r.bit e then (r.label e.1).1=(r.label e.2).1 ∧ (r.label e.1).2≠(r.label e.2).2
  else (r.label e.1).2=(r.label e.2).2 ∧ (r.label e.1).1≠(r.label e.2).1

def minorityMass (M : IncidencePiece K) (r : CoordinateLevel L) :=
  M.edgeProb (fun e => r.bit e≠r.majority)

def inconsistentMass (M : IncidencePiece K) (r : CoordinateLevel L) :=
  M.edgeProb (fun e => ¬r.consistent e)

private lemma edge_cover (M : IncidencePiece K) (A B C : Plane×Plane → Prop)
    (h : ∀e,A e → B e ∨ C e) : M.edgeProb A≤M.edgeProb B+M.edgeProb C := by
  unfold edgeProb
  rw [←add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simp only [natCast_card_filter,←sum_add_distrib]
  apply sum_le_sum
  intro e _
  by_cases ha : A e
  · rcases h e ha with hb|hc
    · by_cases hc : C e <;> simp [ha,hb,hc]
    · by_cases hb : B e <;> simp [ha,hb,hc]
  · by_cases hb : B e <;> by_cases hc : C e <;> simp [ha,hb,hc]

theorem majority_mismatch (M : IncidencePiece K) (r : CoordinateLevel L) :
    M.labelMismatch (r.selected,r.selected)≤M.minorityMass r+M.inconsistentMass r := by
  apply edge_cover
  intro e hn
  cases hb : r.bit e <;> cases hm : r.majority <;> simp_all [CoordinateLevel.selected,CoordinateLevel.consistent]


end
end PlanarUnitDistances.Competition.IncidencePiece
