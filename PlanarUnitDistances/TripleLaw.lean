import PlanarUnitDistances.IncidenceModel

namespace PlanarUnitDistances.Competition.IncidencePiece
open Finset
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

theorem mass_nonnegative (M : IncidencePiece K) (x : Triple M) : 0 ≤ M.mass x := by
  unfold mass
  split_ifs <;> positivity

/-- Summing the actual center degrees recovers the original edge set. -/
theorem sum_degrees (M : IncidencePiece K) : ∑ q ∈ M.Q, M.degreeQ q = M.E.card := by
  have full : ((M.P×ˢM.Q).filter (fun e => e∈M.E))=M.E := by
    ext x
    exact mem_filter.trans (and_iff_right_of_imp (fun h => M.membership h))
  rw [←full] 
  simp only [degreeQ,card_filter,sum_product_right]

/-- Under the original nonempty edge set the common-center sampling expression
has total probability exactly one. Vertices of degree zero require no division
hypothesis and contribute zero. -/
theorem mass_total (M : IncidencePiece K) (hn : M.E.Nonempty) : ∑ x, M.mass x = 1 := by
  have he : (M.E.card:ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hn).ne'
  let bit (p : M.P) (q : M.Q) : ℝ := if (p.val,q.val)∈M.E then 1 else 0
  have fiber (q : M.Q) : ∑ p, bit p q = (M.degreeQ q:ℝ) := by
    change (∑ p : M.P, if (p.val,q.val)∈M.E then (1:ℝ) else 0) = _
    rw [sum_coe_sort M.P (fun p => if (p,q.val)∈M.E then (1:ℝ) else 0)]
    simp only [degreeQ,natCast_card_filter]
  have one (p : M.P) (q : M.Q) (r : M.P) :
      M.mass (p,q,r) = bit p q*bit r q/((M.E.card:ℝ)*M.degreeQ q) := by
    by_cases h : (p.val,q.val)∈M.E <;> by_cases k : (r.val,q.val)∈M.E <;> simp [bit,mass,h,k]
  have pair (q : M.Q) : (∑ p,∑ r,M.mass (p,q,r))=(M.degreeQ q:ℝ)/M.E.card := by
    simp_rw [one, ←Finset.sum_div, ←Finset.mul_sum, fiber, ←Finset.sum_mul, fiber]
    by_cases hd : M.degreeQ q = 0
    · simp [hd]
    · have hd' : (M.degreeQ q:ℝ) ≠ 0 := by exact_mod_cast hd
      field_simp
  have allDeg : ∑ q : M.Q, (M.degreeQ q:ℝ)=(M.E.card:ℝ) := by
    rw [sum_coe_sort M.Q (fun q => (M.degreeQ q:ℝ))]
    exact_mod_cast sum_degrees M
  calc
    _ = ∑ p, ∑ q, ∑ r, M.mass (p,q,r) := by simp only [Fintype.sum_prod_type]
    _ = ∑ q, ∑ p, ∑ r, M.mass (p,q,r) := Finset.sum_comm
    _ = ∑ q : M.Q, (M.degreeQ q:ℝ)/M.E.card := by simp_rw [pair]
    _ = 1 := by rw [←Finset.sum_div,allDeg,div_self he]

end
end PlanarUnitDistances.Competition.IncidencePiece
