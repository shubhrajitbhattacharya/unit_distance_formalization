import PlanarUnitDistances.ArithmeticLevels
import PlanarUnitDistances.ThresholdInterval

namespace PlanarUnitDistances.Competition.IncidencePiece
open NumberField Real
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

theorem finite_edge_bit (M : IncidencePiece K) (v : FinitePlace K) (s : ℝ)
    (e : Plane×Plane) (he : e∈M.E) : (finiteRecord M v s).bit e=decide (s<M.threshold v e) := by
  change (if h : e∈M.E then (fun (a : M.E) => decide (s<M.threshold v a.val)) ⟨e,h⟩ else false)=_
  simp [he]

theorem supported_edges (M : IncidencePiece K) (x : Triple M) (hx : 0<M.mass x) :
    (x.1.val,x.2.1.val)∈M.E ∧ (x.2.2.val,x.2.1.val)∈M.E := by
  by_contra h; simp [mass,h] at hx

theorem ratio_ne (M : IncidencePiece K) (x : Triple M) (hx : 0<M.mass x) :
    tripleRatio M x≠0 := (supported_chord M x hx).1

theorem threshold_ratio (M : IncidencePiece K) (x : Triple M) (hx : 0<M.mass x) (v : AbsoluteValue K ℝ) :
    Real.log (v (tripleRatio M x))=M.threshold v (x.2.2.val,x.2.1.val)-M.threshold v (x.1.val,x.2.1.val) := by
  obtain ⟨p,q⟩ := supported_edges M x hx
  have h₁ := (v.pos (left_ne_zero_of_mul_eq_one (unit_model M p))).ne'
  have h₂ := (v.pos (left_ne_zero_of_mul_eq_one (unit_model M q))).ne'
  unfold tripleRatio threshold
  rw [map_div₀,Real.log_div h₁ h₂]; ring

end
end PlanarUnitDistances.Competition.IncidencePiece
