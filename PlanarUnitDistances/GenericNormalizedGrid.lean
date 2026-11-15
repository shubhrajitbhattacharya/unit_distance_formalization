import PlanarUnitDistances.GenericGridPoint
import PlanarUnitDistances.GenericAnchorField
import PlanarUnitDistances.NormalizedRowField
import PlanarUnitDistances.LiftedTangentData

namespace PlanarUnitDistances.Competition.GenericCurvePoint
open MvPolynomial GridElimination LiftedTangent Set
noncomputable section
variable {E : Type} [Field E] [Algebra ℂ E] [IsAlgClosed E]

/-- The normalized coefficient field, row, and velocities on the same
generic point. The anchor positions are recorded in both coordinate systems. -/
structure NormalizedRow (y : LiftCoord → E) where
  K : IntermediateField ℂ E
  closed : IsAlgClosed K
  i : Fin 8
  transcendental : Transcendental K (nullPos y (.inl i) 0)
  anchor : ∀ j d,nullPos y (.inr j) d∈K
  cartesian : ∀ j d,cart y (.inr j) d∈K
  h : Fin 8 → Fin 2 → E
  v : Fin 4 → Fin 2 → E
  t : Fin 8 → E
  b : Fin 4 → E
  tangent : GenericParameters.Compatible (fun i => cart y (.inl i)) (fun j => cart y (.inr j))
    (fun i j => μ y i j-u y i j) h v t b
  velocity : ∀ j d,v j d ∈ K
  scalar : ∀ j,b j ∈ K

theorem normalized_of_lift {f g : Poly₂} (ng : g≠0) {y : LiftCoord → E}
    (data : Data f g y) (ind : AlgebraicIndependent ℂ (fun s : Slot => nullPos y s 0)) :
    Nonempty (NormalizedRow y) := by
  let z (s : Slot) := nullPos y s 0
  let B := IntermediateField.adjoin ℂ (range (fun j : Fin 4 => z (.inr j)))
  let C := _root_.algebraicClosure B E
  let F := C.restrictScalars ℂ
  have curve (j : Fin 4) : aeval ![z (.inr j),nullPos y (.inr j) 1] g=0 := by
    have e : ![z (.inr j),nullPos y (.inr j) 1]=nullPos y (.inr j) := by
      funext d; fin_cases d <;> rfl
    rw [e]; exact data.anchor_curve j
  obtain ⟨left,right⟩ := GenericAnchorField.anchor_coordinates z _ ind g ng curve
  have mem (j : Fin 4) (d : Fin 2) : nullPos y (.inr j) d∈F := by
    fin_cases d
    · exact C.algebraMap_mem (⟨_,IntermediateField.subset_adjoin _ _ ⟨j,rfl⟩⟩ : B)
    · exact right j
  have cp (j : Fin 4) (d : Fin 2) : cart y (.inr j) d∈F := by
    fin_cases d
    · exact F.mul_mem (F.algebraMap_mem _) (F.add_mem (mem j 0) (mem j 1))
    · exact F.mul_mem (F.algebraMap_mem _) (F.sub_mem (mem j 0) (mem j 1))
  have diff : cart y (.inr 1) ≠ cart y (.inr 0) := by
    intro eq
    have same : nullPos y (.inr 1) 0 = nullPos y (.inr 0) 0 := by
      rw [← (recover y (.inr 1)).1,← (recover y (.inr 0)).1,eq]
    exact (by decide : (Sum.inr 1 : Slot) ≠ .inr 0) (ind.injective same)
  have positions j d : cart y (.inr j) d∈range (algebraMap F E) := ⟨⟨_,cp j d⟩,rfl⟩
  obtain ⟨L,closed,i,h,v,t,b,he,hc,hv,hs,tr⟩ := GenericParameters.normalized_row_field
    positions data.compatible diff (show AlgebraicIndependent F (fun i => z (.inl i)) from left)
  have allanchors j d : nullPos y (.inr j) d∈L := L.algebraMap_mem (⟨_,mem j d⟩ : F)
  exact ⟨⟨L.restrictScalars ℂ,closed,i,tr,allanchors,hc,h,v,t,b,he,hv,hs⟩⟩


end
end PlanarUnitDistances.Competition.GenericCurvePoint
