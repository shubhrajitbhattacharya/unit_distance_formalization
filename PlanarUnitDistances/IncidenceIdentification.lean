import PlanarUnitDistances.CircleSampling
import PlanarUnitDistances.TripleLaw

namespace PlanarUnitDistances.Competition.IncidencePiece
open Finset
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
namespace Research
open OAI.PlanarUnitDistances.CircleIncidence

/-- The extra condition used in identifying the explicitly stored edge
set with the research graph is inclusion of every available unit edge. -/
def Full (M : IncidencePiece K) : Prop :=
  ∀p∈M.P,∀q∈M.Q,dist p q=1 → (p,q)∈M.E

theorem point_degree (M : IncidencePiece K) (h : Full M) (p : Plane) (hp : p∈M.P) :
    (M.degreeP p:ℝ)=degree M.Q p := by
  have eq : M.Q.filter (fun q => (p,q)∈M.E)=M.Q.filter (fun q => dist q p=1) := by
    apply filter_congr
    intro q hq
    exact ⟨fun he => (dist_comm q p).trans (M.unit (p,q) he),
      fun hd => h p hp q hq ((dist_comm p q).trans hd)⟩
  exact congrArg (fun A : Finset Plane => (A.card:ℝ)) eq

theorem center_degree (M : IncidencePiece K) (h : Full M) (q : Plane) (hq : q∈M.Q) :
    (M.degreeQ q:ℝ)=degree M.P q := by
  unfold degreeQ degree
  congr 2
  apply filter_congr
  intro p hp
  exact ⟨M.unit _,h p hp q hq⟩

theorem edge_count (M : IncidencePiece K) (h : Full M) :
    (M.E.card:ℝ)=OAI.PlanarUnitDistances.CircleIncidence.incidences M.P M.Q := by
  rw [←sum_degrees M,Nat.cast_sum]
  exact sum_congr rfl (fun q hq => center_degree M h q hq)

theorem point_marginal (M : IncidencePiece K) (h : Full M) (p : M.P) :
    M.mu p=degree M.Q p/OAI.PlanarUnitDistances.CircleIncidence.incidences M.P M.Q := by
  rw [mu,point_degree M h p p.prop,edge_count M h]

theorem center_marginal (M : IncidencePiece K) (h : Full M) (q : M.Q) :
    M.kappa q=degree M.P q/OAI.PlanarUnitDistances.CircleIncidence.incidences M.P M.Q := by
  rw [kappa,center_degree M h q q.prop,edge_count M h]

/-- Compare each atom, including both the diagonal and nonincident triples,
in the two index conventions, before performing any expectation. -/
theorem atom (M : IncidencePiece K) (h : Full M) (p r : M.P) (q : M.Q) :
    M.mass (p,q,r) = if dist p.val q.val=1 ∧ dist r.val q.val=1 then
      (OAI.PlanarUnitDistances.CircleIncidence.incidences M.P M.Q*degree M.P q)⁻¹ else 0 := by
  unfold mass
  have eqv (a : M.P) : (a.val,q.val)∈M.E ↔ dist a.val q.val=1 := ⟨M.unit _,h _ a.prop _ q.prop⟩
  simp only [eqv,edge_count M h,center_degree M h q q.prop,one_div]

end Research
end
end PlanarUnitDistances.Competition.IncidencePiece
