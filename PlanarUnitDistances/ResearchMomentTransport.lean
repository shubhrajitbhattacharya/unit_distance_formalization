import PlanarUnitDistances.ResearchPhysicalScores
import PlanarUnitDistances.TripleSelection

namespace PlanarUnitDistances.ResearchPhysical
open OAI.PlanarUnitDistances CommonFieldModel OAI.PlanarUnitDistances.CircleIncidence
open ProofAssembly Finset
open scoped Classical
noncomputable section
variable {P Q : Finset Competition.Plane}

theorem atom_eq_tripleWeight (M : Model P Q) (x : UnitTriple P Q) :
    (toPiece M).mass (reorder M x) = tripleWeight P Q x := by
  obtain ⟨⟨p,r⟩,q⟩ := x
  change (toPiece M).mass (p,q,r) = _
  have ha := Competition.IncidencePiece.Research.atom (toPiece M) (full M) p r q
  apply ha.trans
  change (if dist p.val q.val=1 ∧ dist r.val q.val=1 then (incidences P Q*degree P q)⁻¹ else 0) = _
  simp only [tripleWeight,unitRows,unitNeighbors,mem_filter,mem_univ,true_and]

theorem reindex_expectation (M : Model P Q) (F : Competition.Triple (toPiece M) → ℝ) :
    (∑ x : UnitTriple P Q, tripleWeight P Q x*F (reorder M x)) =
      ∑ y, (toPiece M).mass y*F y := by
  simp_rw [←atom_eq_tripleWeight M]
  exact reorder_sum M (fun y => (toPiece M).mass y*F y)

private theorem physical_epsilon : Competition.eps = comparisonEpsilon := by
  unfold Competition.eps comparisonEpsilon
  rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
  norm_num

/-- A physical endpoint model for the same unit graph gives every field
of the original comparison-moment statement. The equality of scales is
exposed so construction of the arithmetic threshold measure is independent
of this finite-law and norm comparison. -/
theorem comparison_moments_of_bounds (M : Model P Q) (d : Competition.Scores (toPiece M))
    (b : Competition.MomentBounds (toPiece M) d) (he : 0 < incidences P Q)
    (hs : (toPiece M).scale=pieceScale M) : ComparisonMoments M := by
  have hQ : Q.Nonempty := by
    by_contra h
    have e := not_nonempty_iff_eq_empty.mp h
    simp [e,incidences] at he
  let Z (x : UnitTriple P Q) := d.error (reorder M x)
  refine ⟨d.H,endpoint M d,Z,endpoint_width_nonnegative M d b hQ,endpoint_finite M d,
    fun x => b.error_nn (reorder M x),?_,?_,?_,?_⟩
  · have hh := b.mean
    rw [hs,←reindex_expectation M d.width] at hh
    exact hh
  · have hh := b.tail
    rw [hs,physical_epsilon,←reindex_expectation M
      (fun y => if 8*pieceScale M/comparisonEpsilon<d.width y then d.width y else 0)] at hh
    exact hh
  · have hh := b.error
    rw [hs,←reindex_expectation M d.error] at hh
    exact hh
  · rintro ⟨⟨p,r⟩,q⟩ hx
    have hm : 0<(toPiece M).mass (p,q,r) := by
      exact (atom_eq_tripleWeight M ((p,r),q)).symm ▸ hx
    have inc : p∈unitRows P Q q ∧ r∈unitRows P Q q := by
      by_contra h
      simp [tripleWeight,h] at hx
    have nz := (centerRatio_spec M inc.1 inc.2).1
    refine ⟨unsigned_lower M d b p r q hm nz,?_⟩
    exact (signed_eq M d p r q) ▸ b.signed (p,q,r) hm

end
end PlanarUnitDistances.ResearchPhysical

