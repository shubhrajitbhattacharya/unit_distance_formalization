import PlanarUnitDistances.ResearchPhysicalModel
import PlanarUnitDistances.PhysicalLabels
import PlanarUnitDistances.DominantUniqueness

namespace PlanarUnitDistances.ResearchPhysical
open OAI.PlanarUnitDistances CommonFieldModel Competition NumberField
open PhysicalLabels PosteriorPlaces Finset
open scoped Classical
noncomputable section
variable {P Q : Finset Competition.Plane}

/-- The tagged point and center copies can represent the same physical
vertex when P and Q intersect. -/
def planeVertex : P ⊕ Q → Competition.Plane := Sum.elim Subtype.val Subtype.val

theorem planeVertex_mem (x : P⊕Q) : planeVertex x∈P∪Q := by
  cases x with
  | inl p => exact mem_union_left _ p.prop
  | inr q => exact mem_union_right _ q.prop

theorem vertex_z (M : Model P Q) (x : P⊕Q) : (toPiece M).Z (planeVertex x)=M.z x := by
  cases x with
  | inl p => exact z_point M p
  | inr q => exact z_center M q

theorem vertex_w (M : Model P Q) (x : P⊕Q) : (toPiece M).W (planeVertex x)=M.w x := by
  apply Subtype.ext
  cases x with
  | inl p => exact ((toPiece M).coordinates _ (mem_union_left _ p.prop)).2.trans (M.w_eq (.inl p)).symm
  | inr q => exact ((toPiece M).coordinates _ (mem_union_right _ q.prop)).2.trans (M.w_eq (.inr q)).symm

/-- Equality of each coordinate class in the two record encodings,
at an arbitrary shift and level of the original infinite place. -/
theorem arch_coordinate_classes (M : Model P Q) (v : InfinitePlace M.field)
    (U V : ℝ×ℝ) (s : ℝ) (x y : P⊕Q) :
    let a := (toPiece M).archRecord v U V s
    let b := archPair v U V M.z M.w s
    ((a.label (planeVertex x)).1=(a.label (planeVertex y)).1 ↔ (b x).1=(b y).1) ∧
    ((a.label (planeVertex x)).2=(a.label (planeVertex y)).2 ↔ (b x).2=(b y).2) := by
  dsimp only
  obtain ⟨z,w⟩ := (toPiece M).arch_matches v U V s _ _ (planeVertex_mem x) (planeVertex_mem y)
  rw [z,w]
  simp only [archPair,archLabel_eq,archMatch,GridShift.gridLabel,IncidencePiece.grid,vertex_z,vertex_w,and_self,iff_self]

/-- At a finite place the same assertion is equality of ultrametric
ball membership for the original coordinates, with the boundary included. -/
theorem finite_coordinate_classes (M : Model P Q) (v : FinitePlace M.field)
    (s : ℝ) (x y : P⊕Q) :
    let a := (toPiece M).finiteRecord v s
    let b := finitePair v M.z M.w s
    ((a.label (planeVertex x)).1=(a.label (planeVertex y)).1 ↔ (b x).1=(b y).1) ∧
    ((a.label (planeVertex x)).2=(a.label (planeVertex y)).2 ↔ (b x).2=(b y).2) := by
  dsimp only
  obtain ⟨z,w⟩ := (toPiece M).finite_matches v s _ _ (planeVertex_mem x) (planeVertex_mem y)
  rw [z,w]
  simp only [finitePair,finiteLabel_eq,finiteMatch,vertex_z,vertex_w,and_self,iff_self]

end
end PlanarUnitDistances.ResearchPhysical
