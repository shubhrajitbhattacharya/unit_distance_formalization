import PlanarUnitDistances.BlockMacaulay
import Mathlib

namespace PlanarUnitDistances.MacaulayFactorBounds
open HomogeneousMacaulay BlockMacaulay MvPolynomial Finset
open scoped Classical Matrix
noncomputable section

theorem rows_le (q : ℕ) (hq : q ≤ 98) : Fintype.card (Row q) ≤ 2^200 := by
  rw [matrix_size]
  exact (Nat.choose_le_two_pow ..).trans (Nat.pow_le_pow_right (by decide) (by omega))

theorem mon_count_le {q : ℕ} (hq : q ≤ 98) (i : Coord q) :
    Fintype.card (Mon q (formDegree i)) ≤ 2^101 := by
  rw [Fintype.card_coe, card_finsuppAntidiag_nat_eq_choose]
  simp only [card_univ, Fintype.card_option, Fintype.card_fin]
  apply (Nat.choose_le_two_pow ..).trans
  apply Nat.pow_le_pow_right (by decide)
  cases i <;> simp only [formDegree] <;> omega

theorem parameter_count_le {q : ℕ} (hq : q ≤ 98) :
    Fintype.card (Parameter q) ≤ 2^110 := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _ : Coord q, 2^101 := sum_le_sum fun i _ => mon_count_le hq i
    _ ≤ _ := by
      simp only [sum_const, card_univ, Fintype.card_option, Fintype.card_fin, nsmul_eq_mul]
      change (q+1) * 2^101 ≤ 2^110
      omega

theorem minor_totalDegree {q : ℕ} (i : Coord q) :
    (minor i).totalDegree ≤ Fintype.card (Row q) := by
  unfold minor
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro perm _
  rw [Units.smul_def]
  apply (totalDegree_smul_le ..).trans
  apply (totalDegree_finsetProd ..).trans
  calc
    _ ≤ ∑ _ : Row q, 1 := sum_le_sum fun j _ => by
      apply totalDegree_finsetSum_le
      intro k _
      split <;> simp
    _ = _ := by simp

theorem minor_box_bound {q : ℕ} (i : Coord q) (hq : q ≤ 98) (u : Parameter q → ℤ)
    (M : ℕ) (hu : ∀ e, (u e).natAbs ≤ M) :
    (eval u (minor i)).natAbs ≤ (Fintype.card (Row q)).factorial * ((2^101)*M) ^ Fintype.card (Row q) := by
  let A : Coefficients q ℤ := fun j m => u ⟨j,m⟩
  have mapId : Int.castRingHom ℤ = RingHom.id ℤ := by ext; rfl
  have he := eval_minor i A
  rw [mapId] at he
  change eval u (minor i) = (blockMatrix i A).det at he
  rw [he]
  have hb (a b : Row q) : ((blockMatrix i A) a b).natAbs ≤ 2^101 * M := by
    unfold blockMatrix
    apply (Int.natAbs_sum_le ..).trans
    calc
      _ ≤ ∑ _ : Mon q (formDegree (late i a)), M := sum_le_sum fun m _ => by
        split
        · exact hu _
        · simp
      _ ≤ _ := by simpa using Nat.mul_le_mul_right M (mon_count_le hq (late i a))
  have hz := Matrix.det_le (A := blockMatrix i A) (abv := AbsoluteValue.abs)
    (x := ((2^101 * M : ℕ) : ℤ)) (fun a b => by
      change |(blockMatrix i A) a b| ≤ _
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hb a b)
  change |(blockMatrix i A).det| ≤ _ at hz
  rw [Int.abs_eq_natAbs, nsmul_eq_mul] at hz
  exact_mod_cast hz

end
end PlanarUnitDistances.MacaulayFactorBounds
