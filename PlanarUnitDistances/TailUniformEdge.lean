import PlanarUnitDistances.TripleMarginal
import PlanarUnitDistances.Selection

namespace PlanarUnitDistances.Competition.IncidencePiece
open Real Finset
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

def centerFiber (M : IncidencePiece K) (p : M.P) := M.Q.filter (fun q => (p.val,q)∈M.E)
def actualEdge (M : IncidencePiece K) : (Σ p : M.P, M.centerFiber p) ≃ M.E where
  toFun z := ⟨(z.1.val,z.2.val),(mem_filter.mp z.2.prop).2⟩
  invFun e := ⟨⟨e.val.1,(mem_product.mp (M.membership e.prop)).1⟩,
    ⟨e.val.2,mem_filter.mpr ⟨(mem_product.mp (M.membership e.prop)).2,e.prop⟩⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def edgeMean (M : IncidencePiece K) (F : Plane×Plane → ℝ) :=
  ∑ e : M.E, (1/(M.E.card:ℝ))*F e.val

theorem fiber_mean (M : IncidencePiece K) (F : Plane×Plane → ℝ) :
    (∑ e : Σ p : M.P,M.centerFiber p, (1/(M.E.card:ℝ))*F (e.1.val,e.2.val)) = M.edgeMean F :=
  (M.actualEdge.sum_comp (fun e : M.E => (1/(M.E.card:ℝ))*F e.val))

theorem fiber_event (M : IncidencePiece K) (A : Plane×Plane → Prop) :
    eventMass (ι := Σ p : M.P,M.centerFiber p) (fun _ => 1/(M.E.card:ℝ))
      (fun e => A (e.1.val,e.2.val)) = M.edgeProb A := by
  unfold eventMass
  change (∑ e : Σ p : M.P,M.centerFiber p, if A (M.actualEdge e).val then 1/(M.E.card:ℝ) else 0) = _
  rw [M.actualEdge.sum_comp (fun e : M.E => if A e.val then 1/(M.E.card:ℝ) else 0)]
  unfold edgeProb
  rw [sum_coe_sort M.E (fun x => if A x then 1/(M.E.card:ℝ) else 0),←sum_filter]
  simp [nsmul_eq_mul,div_eq_mul_inv]

theorem edgeMean_indicator (M : IncidencePiece K) (A : Plane×Plane → Prop) :
    M.edgeMean (fun e => if A e then (1:ℝ) else 0) = M.edgeProb A := by
  rw [←fiber_mean,←fiber_event]
  simp only [eventMass,mul_ite,mul_one,mul_zero]

/-- The two endpoint marginals agree with the first endpoint of a uniform
edge, for every real-valued function, including truncated endpoint widths. -/
theorem leg_means (M : IncidencePiece K) (F : Plane → ℝ) :
    (∑v : Triple M,M.mass v*F v.1.val) = M.edgeMean (fun e => F e.1) ∧
    (∑v : Triple M,M.mass v*F v.2.2.val) = M.edgeMean (fun e => F e.1) := by
  have decomp (p : M.P) (m : ℝ) :
      m*F p.val = ∑a : M.P, (if p.val=a.val then m else 0)*F a.val := by
    simp only [Subtype.val_inj,ite_mul,zero_mul]
    simp
  have edge : M.edgeMean (fun e => F e.1) =
      ∑ a : M.P, M.edgeProb (fun e => e.1=a.val)*F a.val := by
    unfold edgeMean
    have conv (e : M.E) := decomp (⟨e.val.1,(mem_product.mp (M.membership e.prop)).1⟩ : M.P) (1/(M.E.card:ℝ))
    simp only at conv
    simp_rw [conv]
    rw [sum_comm]
    apply sum_congr rfl
    intro p _
    rw [←sum_mul,←M.edgeMean_indicator (fun e => e.1=p.val)]
    unfold edgeMean
    simp [mul_ite]
  rw [edge]
  have gen (g : Triple M → M.P) (h : ∀a : M.P,
      (∑v : Triple M,if (g v).val=a.val then M.mass v else 0)=M.edgeProb (fun e => e.1=a.val)) :
      (∑ v : Triple M,M.mass v*F (g v).val) = ∑a : M.P,M.edgeProb (fun e => e.1=a.val)*F a.val := by
    simp_rw [decomp (g _) (M.mass _)]
    rw [sum_comm]
    apply sum_congr rfl; intro a _
    rw [←sum_mul,h a]
  constructor
  · apply gen (fun v => v.1)
    intro a
    convert (M.edge_marginals (fun e => e.1=a.val)).1 using 1
    apply sum_congr rfl; intro v _
    by_cases h : v.1.val=a.val <;> simp [h]
  · apply gen (fun v => v.2.2)
    intro a
    convert (M.edge_marginals (fun e => e.1=a.val)).2 using 1
    apply sum_congr rfl; intro v _
    by_cases h : v.2.2.val=a.val <;> simp [h]

/-- Markov bound in the original uniform edge law, with the closed upper
level set to allow the exact center threshold u/12. -/
theorem edge_markov (M : IncidencePiece K) (F : Plane×Plane → ℝ) (hF : ∀e∈M.E,0≤F e)
    {c : ℝ} (_hc : 0≤c) (A : Plane×Plane → Prop) (hA : ∀e∈M.E, A e → c≤F e) :
    c*M.edgeProb A ≤ M.edgeMean F := by
  rw [←M.edgeMean_indicator A]
  unfold edgeMean
  rw [mul_sum]
  apply sum_le_sum
  intro e _
  by_cases hh : A e.val
  · simp only [hh,ite_true,mul_one]
    rw [mul_comm c]
    exact mul_le_mul_of_nonneg_left (hA _ e.prop hh) (by positivity)
  · simp only [hh,ite_false,mul_zero]
    exact mul_nonneg (by positivity) (hF _ e.prop)

end
end PlanarUnitDistances.Competition.IncidencePiece

