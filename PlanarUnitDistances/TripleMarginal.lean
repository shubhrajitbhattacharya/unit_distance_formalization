import PlanarUnitDistances.RareLabels

namespace PlanarUnitDistances.Competition.IncidencePiece
open Finset
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

/-- Integration against either incident edge of the actual two-edge
walk recovers the original *uniform* edge law. -/
theorem edge_marginals (M : IncidencePiece K) (A : Plane×Plane → Prop) :
    (∑v : Triple M,if A (v.1.val,v.2.1.val) then M.mass v else 0)=M.edgeProb A ∧
    (∑v : Triple M,if A (v.2.2.val,v.2.1.val) then M.mass v else 0)=M.edgeProb A := by
  let hit (p : M.P) (q : M.Q) : ℝ := if (p.val,q.val)∈M.E then 1 else 0
  have deg (q : M.Q) : ∑p,hit p q=(M.degreeQ q.val:ℝ) := by
    change (∑p : M.P, if (p.val,q.val)∈M.E then (1:ℝ) else 0)=_
    rw [sum_coe_sort M.P (fun p => if (p,q.val)∈M.E then (1:ℝ) else 0)]
    simp only [degreeQ,natCast_card_filter]
  let W (p : M.P) (q : M.Q) : ℝ := if (p.val,q.val)∈M.E ∧ A (p.val,q.val) then 1 else 0
  have one (p r : M.P) (q : M.Q) : (if A (p.val,q.val) then M.mass (p,q,r) else 0)=
      W p q*hit r q/((M.E.card:ℝ)*M.degreeQ q.val) := by
    by_cases h1 : (p.val,q.val)∈M.E <;> by_cases h2 : (r.val,q.val)∈M.E <;>
      by_cases ha : A (p.val,q.val) <;> simp [mass,W,hit,h1,h2,ha]
  have fiber (p : M.P) (q : M.Q) : (∑r : M.P,if A (p.val,q.val) then M.mass (p,q,r) else 0)=W p q/M.E.card := by
    simp_rw [one,←sum_div,←mul_sum,deg]
    by_cases h : (p.val,q.val)∈M.E ∧ A (p.val,q.val)
    · have hd : M.degreeQ q.val≠0 := card_ne_zero.mpr ⟨p.val,mem_filter.mpr ⟨p.prop,h.1⟩⟩
      have wone : W p q=1 := ite_eq_left h
      rw [wone,one_mul,div_mul_eq_div_div,div_right_comm,div_self (show (M.degreeQ q.val:ℝ)≠0 from Nat.cast_ne_zero.mpr hd)]
    · simp [W,h]
  have ff : (M.P×ˢM.Q).filter (fun e => e∈M.E ∧ A e)=M.E.filter A := by
    ext e; simp only [mem_filter]
    exact ⟨And.right,fun he => ⟨M.membership he.1,he⟩⟩
  have first : (∑v : Triple M,if A (v.1.val,v.2.1.val) then M.mass v else 0)=M.edgeProb A := by
    simp only [Fintype.sum_prod_type,fiber,←sum_div]
    unfold edgeProb
    apply congrArg (·/(M.E.card:ℝ))
    let f (e : Plane×Plane) : ℝ := if e∈M.E ∧ A e then 1 else 0
    have inner (p : M.P) : ∑q : M.Q,W p q=∑q∈M.Q,f (p.val,q) := by
      rw [←sum_coe_sort M.Q (fun q => f (p.val,q))]
    simp_rw [inner]
    rw [sum_coe_sort M.P (fun p => ∑q∈M.Q,f (p,q)),←sum_product (f:=f)]
    unfold f
    rw [←natCast_card_filter,ff]
  refine ⟨first,?_⟩
  let rev : Triple M ≃ Triple M := ⟨fun x => (x.2.2,x.2.1,x.1),fun x => (x.2.2,x.2.1,x.1),fun _ => rfl,fun _ => rfl⟩
  have eq := Fintype.sum_equiv rev
    (fun v : Triple M => if A (v.2.2.val,v.2.1.val) then M.mass v else 0)
    (fun v : Triple M => if A (v.1.val,v.2.1.val) then M.mass v else 0)
    (fun v => by simp only [rev]; by_cases hh : A (v.2.2.val,v.2.1.val) <;> simp [hh,mass,and_comm])
  exact eq.trans first

end
end PlanarUnitDistances.Competition.IncidencePiece
