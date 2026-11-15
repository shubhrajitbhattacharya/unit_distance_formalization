import PlanarUnitDistances.MovingGrid
import PlanarUnitDistances.GraphRestriction
import PlanarUnitDistances.FourAnchorCurve

namespace PlanarUnitDistances.MovingGrid
open OAI.PlanarUnitDistances
open MvPolynomial AnchorGenericPlane CurveReflection CurveRestriction GraphRestriction
open scoped Classical ComplexConjugate
noncomputable section

private theorem null_degree (F : CurveReflection.Poly) : (toNull Complex.I F).totalDegree ≤ F.totalDegree := by
  apply CurveProduct.degree_after_linear_substitution
  intro i
  fin_cases i
  · apply (totalDegree_mul ..).trans
    simpa using (totalDegree_add (X (0:Fin 2) : CurveReflection.Poly) (X 1))
  · change ((C (2*Complex.I)⁻¹)*(X 0-X 1) : CurveReflection.Poly).totalDegree ≤ 1
    refine (totalDegree_mul ..).trans ?_
    rw [totalDegree_C,zero_add]
    exact (totalDegree_sub _ _).trans (by simp)

private theorem null_eval (F : CurveReflection.Poly) (p : Plane) :
    eval (realPoint p) (toNull Complex.I F) = eval (cartPoint p) F := by
  change eval (realPoint p) (eval₂ C _ F) = _
  rw [eval₂_comp_left]
  congr 1
  · ext a; simp
  · funext i
    have h := congrFun (recover_cart p) i
    fin_cases i <;> simpa [GridLocus.cart,div_eq_inv_mul] using h

private theorem trivial_curve {I : Type} [Fintype I] (p : I → Plane) (hc : Fintype.card I ≤ 1) :
    ∃ F : CurveReflection.Poly, F≠0 ∧ F.totalDegree ≤ 80 ∧ ∀ i, eval (realPoint (p i)) F=0 := by
  by_cases hi : Nonempty I
  · let j := Classical.choice hi
    let c := realPoint (p j) 0
    refine ⟨X 0-C c, ?_, (totalDegree_sub _ _).trans (by simp), ?_⟩
    · intro h
      have hz := congrArg (eval (fun _ : Fin 2 => c+1)) h
      simp at hz
    · intro i
      rw [Fintype.card_le_one_iff.mp hc i j]
      simp [c]
  · exact ⟨1,one_ne_zero,by simp,fun i => (hi ⟨i⟩).elim⟩

private theorem cart_inj : Function.Injective cartPoint := by
  intro p q h
  ext j
  simpa [cartPoint] using congrArg Complex.re (congrFun h j)

/-- The four anchors and their velocities are shared across the entire finite
set of source points. One degree-80 polynomial contains every point in null
coordinates, also when the set of rows is empty or a singleton. -/
theorem common_neighbor_curve {I : Type} [Fintype I] (p : I → Plane) (r : Fin 4 → Plane)
    (hr : Function.Injective r) (moving : 2 ≤ Fintype.card I →
      ∃ R : I → Fin 4 → ℂ, Nonempty (Equations p r R)) :
    ∃ F : CurveReflection.Poly, F≠0 ∧ F.totalDegree ≤ 80 ∧ ∀ i, eval (realPoint (p i)) F=0 := by
  by_cases hc : 2 ≤ Fintype.card I
  · obtain ⟨R,⟨e⟩⟩ := moving hc
    have hi : Complex.I^2 = -1 := Complex.I_sq
    obtain ⟨F,hF,df,zeros⟩ := four_anchor_curve Complex.I hi (cartPoint ∘ r) e.U e.a
      (cart_inj.comp hr)
    refine ⟨toNull Complex.I F,?_,(null_degree F).trans df,?_⟩
    · simpa only [map_zero] using (toNull_injective hi).ne hF
    · intro i
      rw [null_eval]
      exact zeros ℂ (RingHom.id ℂ) (cartPoint (p i)) (e.H i) (e.A i) (R i)
        (fun j => e.equation i j) (e.velocity_ne i 3)
  · exact trivial_curve p (by omega)

variable {n : ℕ} {K : Type} [Field K] [NumberField K]

/-- The moving-tangent hypothesis implies the two concrete anchor hypotheses
for the restriction of the original graph, in both orientations. -/
theorem curvesForRows {G : AdmissibleGraph n K} (motion : Motion G) : CurvesForRows G := by
  constructor
  · intro a
    let S := common (rows G) a
    let p (i : S) : Plane := i.val.val
    let r (j : Fin 4) : Plane := (a j).val
    have hi : Function.Injective r := Subtype.val_injective.comp a.injective
    have edges (i : S) (j : Fin 4) : (p i,r j) ∈ G.edges := by
      have h : ∀ j, (p i,r j) ∈ G.edges := by
        simpa [S,common,rows,p,r] using i.prop
      exact h j
    obtain ⟨f,hf,df,hz⟩ := common_neighbor_curve p r hi (fun hc => by
      obtain ⟨L⟩ := motion S (Fin 4) p r hc (by decide) (Or.inr (by decide)) edges
      exact ⟨_,L.equations⟩)
    exact ⟨f,hf,df,fun i h => hz ⟨i,h⟩⟩
  · intro a
    let T := common (reverseRow (rows G) Finset.univ) a
    let p (i : Fin 4) : Plane := (a i).val
    let r (j : T) : Plane := j.val.val
    have hi : Function.Injective p := Subtype.val_injective.comp a.injective
    have edges (i : Fin 4) (j : T) : (p i,r j) ∈ G.edges := by
      have h : ∀ i, (p i,r j) ∈ G.edges := by
        simpa [T,common,reverseRow,rows,p,r] using j.prop
      exact h i
    obtain ⟨f,hf,df,hz⟩ := common_neighbor_curve r p hi (fun hc => by
      obtain ⟨L⟩ := motion (Fin 4) T p r (by decide) hc (Or.inl (by decide)) edges
      obtain ⟨e⟩ := L.equations
      exact ⟨_,⟨e.transpose⟩⟩)
    exact ⟨f,hf,df,fun j h => hz ⟨j,h⟩⟩

end
end PlanarUnitDistances.MovingGrid
