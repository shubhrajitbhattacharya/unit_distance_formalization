import PlanarUnitDistances.AnchorNormalization

namespace PlanarUnitDistances.GenericParameters
open Set IntermediateField
noncomputable section

/-- One normalized row over a single algebraically closed coefficient
field inside the actual solution. Every anchor position and every anchor
velocity and scalar belongs to it. The abscissa of the chosen point
remains transcendental over this very field. -/
theorem normalized_row_field {F E : Type*} [Field F] [Field E] [Algebra F E] [IsAlgClosed E]
    {p : Fin 8 → Fin 2 → E} {r : Fin 4 → Fin 2 → E} {R H U A a}
    (positions : ∀ j d,r j d ∈ range (algebraMap F E))
    (eqs : Compatible p r R H U A a) (distinct : r 1 ≠ r 0)
    {x : Fin 8 → E} (ind : AlgebraicIndependent F x) :
    ∃ (K : IntermediateField F E) (_ : IsAlgClosed K) (i : Fin 8)
        (H' : Fin 8 → Fin 2 → E) (U' : Fin 4 → Fin 2 → E) (A' : Fin 8 → E) (a' : Fin 4 → E),
      Compatible p r R H' U' A' a' ∧ (∀ j d,r j d ∈ K) ∧
        (∀ j d,U' j d∈K) ∧ (∀ j,a' j∈K) ∧ Transcendental K (x i) := by
  obtain ⟨t,H',U',A',a',he,hU,ha,i,hi⟩ := normalize_four_anchors eqs distinct ind
  let L := IntermediateField.adjoin F (range t)
  let C := _root_.algebraicClosure L E
  let K := C.restrictScalars F
  have incl {v : E} (h : v∈L) : v∈K := C.algebraMap_mem ⟨v,h⟩
  refine ⟨K,(IsAlgClosure.isAlgClosed L : IsAlgClosed C),i,H',U',A',a',he,?_,
    fun j d => incl (hU j d),fun j => incl (ha j),hi⟩
  intro j d
  obtain ⟨v,h⟩ := positions j d
  exact h ▸ K.algebraMap_mem v

end
end PlanarUnitDistances.GenericParameters
