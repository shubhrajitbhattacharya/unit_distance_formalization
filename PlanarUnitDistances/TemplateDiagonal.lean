import PlanarUnitDistances.ListComparisons

namespace OAI.PlanarUnitDistances.TemplateCoupling
open FiniteLaw FiniteStarCoupling Finset
open scoped Classical
noncomputable section
variable {P Q T : Type*} [Fintype P] [Fintype Q] [Fintype T]

/-- Colliding neighbors in the actual template-conditioned point experiment.
The exceptional width of the base point may be arbitrarily correlated with
its degree and its posterior. The inequality holds separately at every base. -/
theorem slice_collision_at (π : Law (P×Q)) (a : Q → Law T) (p : P) {m : ℝ}
    (atom : ∀q,(row π p).val q≤m) :
    (∑ t,(templates π a).val t*(left (slice π a t)).val p*
      ∑q,((row (slice π a t) p).val q)^2) ≤ Fintype.card T*((left π).val p*m) := by
  have single (t : T) : (templates π a).val t*(left (slice π a t)).val p*
      ∑q,((row (slice π a t) p).val q)^2 ≤ (left π).val p*m := by
    let σ := slice π a t
    have scale (q : Q) : (templates π a).val t*((left σ).val p*(row σ p).val q)≤(left π).val p*m := by
      rw [row_weight,slice_weight]
      have alg : (a q).val t≤1 := (a q).total ▸
        Finset.single_le_sum (fun k _ => (a q).nonneg k) (mem_univ t)
      calc
        _ ≤ π.val (p,q) := mul_le_of_le_one_right (π.nonneg _) alg
        _ = (left π).val p*(row π p).val q := (row_weight π p q).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (atom q) ((left π).nonneg p)
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑q,((left π).val p*m)*(row σ p).val q := by
        apply Finset.sum_le_sum; intro q _
        exact (by simpa only [pow_two,mul_assoc] using
          mul_le_mul_of_nonneg_right (scale q) ((row σ p).nonneg q))
      _ = _ := by rw [←Finset.mul_sum,(row σ p).total,mul_one]
  calc
    _ ≤ ∑ _ : T,(left π).val p*m := Finset.sum_le_sum (fun t _ => single t)
    _ = _ := by simp


end
end OAI.PlanarUnitDistances.TemplateCoupling
