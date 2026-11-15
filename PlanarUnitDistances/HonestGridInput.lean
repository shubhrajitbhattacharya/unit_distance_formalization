import PlanarUnitDistances.IntegralGridFlatten
import PlanarUnitDistances.IntegralGridTable
import PlanarUnitDistances.IntegerCoordinateSplit

namespace PlanarUnitDistances.IntegralGrid
open MvPolynomial EliminantHeight Finset
open TorusCritical (Coord Equation RatioParameters)
noncomputable section

/-- Exactly one parameter per mixing row, the chosen coordinate basis, and the signed labels. -/
abbrev Honest (q : ℕ) (S U : Type*) := (Fin q ⊕ S) ⊕ U
abbrev Ambient (q : ℕ) (S U : Type*) := Fin q ⊕ Honest q S U
variable {V U E : Type*} {q : ℕ}

def role (S : Set V) (free : (↑Sᶜ) ≃ Fin q) : U ⊕ V → Ambient q S U := by
  classical
  exact Sum.elim (fun u => .inr (.inr u)) (fun x => if h : x ∈ S then
    .inr (.inl (.inr ⟨x,h⟩)) else .inl (free ⟨x,h⟩))

def honestRow [Fintype E] (p : E → InStates U V) (S : Set V) (free : (↑Sᶜ) ≃ Fin q)
    (index : E → ℕ) (i : Fin q) : Labels (Ambient q S U) :=
  ∑ e, X (.inr (.inl (.inl i)))^(index e) * rename (role S free) (flatten (p e))

def honestEntry [Fintype E] (p : E → InStates U V) (S : Set V) (free : (↑Sᶜ) ≃ Fin q)
    (index : E → ℕ) (i : Fin q) (d : Fin q →₀ ℕ) : Labels (Honest q S U) :=
  ((sumAlgEquiv ℤ (Fin q) (Honest q S U)) (honestRow p S free index i)).coeff d

private theorem recode_cost {Z : Type*} (p : Labels U) (v : U → Z) :
    coefficientSum (rename v p) ≤ coefficientSum p := by
  have h := coefficientSum_substitution_le p (fun t => (X (v t) : Labels Z))
    (M:=1) (by decide) (fun t => (label_cost _).le)
  rw [rename_eq_aeval,aeval_def,MvPolynomial.algebraMap_eq]
  simpa only [one_pow,mul_one,Function.comp_def] using h

theorem honest_budget [Fintype E] [Fintype V] [Fintype U] (p : E → InStates U V)
    {n : ℕ} (h : ∀ t, Bound n (p t)) (deg : ∀t,(p t).totalDegree≤2)
    (S : Set V) (free : (↑Sᶜ) ≃ Fin q) (index : E → ℕ) (hi : ∀t,index t≤97)
    (i : Fin q) (d : Fin q →₀ ℕ) :
    (honestEntry p S free index i d).totalDegree ≤ 100 ∧
    coefficientSum (honestEntry p S free index i d) ≤ Fintype.card E * (3^Fintype.card V*n) := by
  classical
  constructor
  · apply (IntegralCoordinateSplit.sum_coeff_degree ..).trans
    apply totalDegree_finsetSum_le
    intro t _
    apply (totalDegree_mul ..).trans
    have ha := totalDegree_pow (X (.inr (.inl (.inl i)) : Ambient q S U) : Labels _) (index t)
    rw [totalDegree_X] at ha
    have hb := (totalDegree_rename_le (role S free) _).trans (flatten_degree (h t) (deg t))
    have ht := hi t
    omega
  · apply (IntegralCoordinateSplit.sum_coeff_bound ..).trans
    apply (coefficientSum_sum_le ..).trans
    calc
      _ ≤ ∑ _ : E, 3^Fintype.card V*n := by
        apply sum_le_sum
        intro t _
        apply (coefficientSum_mul_le ..).trans
        have mono : coefficientSum ((X (.inr (.inl (.inl i)) : Ambient q S U) : Labels _) ^ index t) ≤ 1 :=
          (coefficientSum_pow_le ..).trans (by simp [label_cost])
        simpa only [one_mul] using Nat.mul_le_mul mono
          ((recode_cost _ (role S free)).trans (flatten_cost (h t) (deg t)))
      _ = _ := by simp

theorem honest_actual_budget {I J : Type*} [Fintype I] [Fintype J] {r : ℕ}
    (i : I) (j : Option J) (pick : Fin r → Equation I J) (hr : r≤47)
    (hq : Fintype.card (Slots I J r)≤98) (S : Set (Slots I J r)) (free : (↑Sᶜ) ≃ Fin q)
    (index : Input I J r → ℕ) (hi : ∀t,index t≤97) (row : Fin q) (d : Fin q →₀ ℕ) :
    let P := honestEntry (table i j pick) S free index row d
    P.totalDegree ≤ 100 ∧ coefficientSum P ≤ 2^173 := by
  obtain ⟨degree,cost⟩ := honest_budget _ (table_bound i j pick hr) (table_state_degree i j pick) S free index hi row d
  have hrows : Fintype.card (Input I J r)≤98 := by
    simpa only [Input,Slots,CriticalLocus.Variables,Fintype.card_sum,Fintype.card_unit,Nat.add_comm,
      Nat.add_left_comm,Nat.add_assoc] using hq
  have bound : Fintype.card (Input I J r)*(3^Fintype.card (Slots I J r)*1130) ≤ 98*(3^98*1130) :=
    Nat.mul_le_mul hrows (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hq))
  exact ⟨degree,cost.trans (bound.trans (by decide))⟩

end
end PlanarUnitDistances.IntegralGrid
