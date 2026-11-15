import PlanarUnitDistances.ErrorRecord
import PlanarUnitDistances.TripleMarginal
import PlanarUnitDistances.RecordBudget

namespace PlanarUnitDistances.Competition.IncidencePiece
open Finset
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K] {L : Type*}

def walkLinear (M : IncidencePiece K) : (Triple M→ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑v,M.mass v*f v
  map_add' f g := by simp [mul_add,sum_add_distrib]
  map_smul' c f := by simp only [Pi.smul_apply,smul_eq_mul,mul_sum,RingHom.id_apply]; apply sum_congr rfl; intro _ _; ring

theorem walkLinear_const (M : IncidencePiece K) (hn : M.E.Nonempty) (a : ℝ) :
    M.walkLinear (fun _=>a)=a := by
  change ∑v,M.mass v*a=a
  rw [←sum_mul,mass_total M hn,one_mul]

private def mark {X : Type*} (A : X→Prop) (v : X) : ℝ := if A v then 1 else 0

private lemma walk_indicator (M : IncidencePiece K) (A : Triple M→Prop) :
    M.walkLinear (mark A)=(∑v,if A v then M.mass v else 0) := by
  unfold walkLinear
  simp only [mark,LinearMap.coe_mk,AddHom.coe_mk,mul_ite,mul_one,mul_zero]

/-- Average the local two-edge errors on the actual triple experiment.
The coefficients account for the two incident edges and the repeated
endpoint term. Both halves have the same original uniform edge law. -/
theorem average_rare_error (M : IncidencePiece K) (r : CoordinateLevel L) (a : L) :
    M.walkLinear (rareTripleError r a) =
      4*M.edgeException r a+4*M.inconsistentMass r+2*M.walkException r a := by
  let J (e : Plane×Plane) := r.selected e.1≠a ∧ r.selected e.2≠a
  let I (e : Plane×Plane) := ¬r.consistent e
  let Jp := mark (fun v : Triple M => J (v.1.val,v.2.1.val))
  let Jr := mark (fun v : Triple M => J (v.2.2.val,v.2.1.val))
  let Ip := mark (fun v : Triple M => I (v.1.val,v.2.1.val))
  let Ir := mark (fun v : Triple M => I (v.2.2.val,v.2.1.val))
  let X := mark (fun v : Triple M => r.selected v.1.val≠a ∧ r.selected v.2.2.val≠a)
  have rep : (rareTripleError r a : Triple M → ℝ)=(2:ℝ) • (Jp+Jr+Ip+Ir)+(2:ℝ) • X := by
    funext v
    by_cases hp : r.selected v.1.val=a <;> by_cases hq : r.selected v.2.1.val=a <;>
      by_cases hr : r.selected v.2.2.val=a <;> by_cases ep : r.consistent (v.1.val,v.2.1.val) <;>
      by_cases er : r.consistent (v.2.2.val,v.2.1.val) <;>
      norm_num [rareTripleError,CoordinateLevel.twoEdgeError,CoordinateLevel.exceptionAt,
        CoordinateLevel.errorAt,Jp,Jr,Ip,Ir,X,mark,J,I,hp,hq,hr,ep,er]
  have j1 : M.walkLinear Jp=M.edgeException r a := (walk_indicator M _).trans (edge_marginals M J).1
  have j2 : M.walkLinear Jr=M.edgeException r a := (walk_indicator M _).trans (edge_marginals M J).2
  have i1 : M.walkLinear Ip=M.inconsistentMass r := (walk_indicator M _).trans (edge_marginals M I).1
  have i2 : M.walkLinear Ir=M.inconsistentMass r := (walk_indicator M _).trans (edge_marginals M I).2
  have xx : M.walkLinear X=M.walkException r a := by
    rw [show M.walkLinear X=_ from walk_indicator M (fun v => r.selected v.1.val≠a ∧ r.selected v.2.2.val≠a)]
    unfold walkException
    apply sum_congr rfl; intro v _
    by_cases ex : r.selected v.1.val≠a ∧ r.selected v.2.2.val≠a <;> simp [ex]
  rw [rep,map_add,map_smul,map_smul,map_add,map_add,map_add,j1,j2,i1,i2,xx]
  simp only [smul_eq_mul]; ring

end
end PlanarUnitDistances.Competition.IncidencePiece
