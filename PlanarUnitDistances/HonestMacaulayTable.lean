import PlanarUnitDistances.HonestGridEvaluation
import PlanarUnitDistances.QuadraticHomogenization
import PlanarUnitDistances.SelectedCriticalLocus

namespace PlanarUnitDistances.IntegralGrid
open MvPolynomial EliminantHeight HomogeneousMacaulay
open TorusCritical (Equation RatioParameters ratioParameterValues)
noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J] {r q w : ℕ}

theorem card_input_eq_slots :
    Fintype.card (Input I J r) = Fintype.card (Slots I J r) := by
  simp only [Input,Slots,CriticalLocus.Variables,Fintype.card_sum,Fintype.card_unit]
  omega

/-- The exponent bound follows from counting the actual original equations. -/
theorem index_budget (ord : Input I J r ≃ Fin w) (hq : Fintype.card (Slots I J r)≤98)
    (e : Input I J r) : (ord e).val≤97 := by
  have hw := Fintype.card_congr ord
  rw [Fintype.card_fin,card_input_eq_slots] at hw
  have := (ord e).isLt
  omega


def honestCoefficients (i : I) (j : Option J) (pick : Fin r → Equation I J)
    (S : Set (Slots I J r)) (free : (↑Sᶜ) ≃ Fin q) (ord : Input I J r ≃ Fin w)
    (out : Fin q) : Coefficients q (Labels (Honest q S (RatioParameters I J)))
  | none, m => if Finsupp.single (some out) 1=m.val then 1 else 0
  | some t, m => honestEntry (table i j pick) S free (fun e => (ord e).val) t m.val.some

theorem honest_coefficients_budget (i : I) (j : Option J) (pick : Fin r → Equation I J)
    (hs : r≤47) (hq : Fintype.card (Slots I J r)≤98)
    (S : Set (Slots I J r)) (free : (↑Sᶜ) ≃ Fin q) (ord : Input I J r ≃ Fin w)
    (out : Fin q) (b : HomogeneousMacaulay.Coord q) (m : Mon q (formDegree b)) :
    let C := honestCoefficients i j pick S free ord out b m
    C.totalDegree ≤ 100 ∧ coefficientSum C ≤ 2^173 := by
  cases b with
  | none =>
    dsimp only [honestCoefficients]
    split <;> simp [coefficientSum]
  | some t => exact honest_actual_budget i j pick hs hq S free _ (index_budget ord hq) t m.val.some

/-- Specialization into the actual coefficient field of the sliced stationary component.
The input has no deformation or test parameter. The test form is the desired
remaining output coordinate. -/
theorem honest_coefficients_evaluation {k : Type*} [Field k] (a : I → Option J → kˣ)
    (i : I) (j : Option J) (pick : Fin r → Equation I J)
    (S : Set (Slots I J r)) (free : (↑Sᶜ) ≃ Fin q) (ord : Input I J r ≃ Fin w)
    (out : Fin q) (mix : Fin q → ℕ) (b : HomogeneousMacaulay.Coord q) (m : Mon q (formDegree b)) :
    let g t := ∑ e, (mix t : MvPolynomial (Fin q) (FrozenField k S)) ^ (ord e).val *
      numbered S free (CriticalLocus.incidenceEquation (TorusCritical.ratio a i j)
        ((TorusCritical.equation a) ∘ pick) id e)
    eval₂Hom (Int.castRingHom (FrozenField k S))
        (honestValue S (ratioParameterValues a) (fun t => (mix t : FrozenField k S)))
        (honestCoefficients i j pick S free ord out b m) =
      UniversalIncidence.inputCoefficients out (fun t => UniversalIncidence.quadraticHomogenization (g t)) b m := by
  intro g
  cases b with
  | none =>
    refine Eq.trans ?_ (UniversalIncidence.input_test_slot out (fun t => UniversalIncidence.quadraticHomogenization (g t)) m).symm
    dsimp only [honestCoefficients]
    split <;> simp
  | some t =>
    exact (honest_actual_evaluation i j pick a S free (fun e => (ord e).val) t m.val.some mix).trans
      (UniversalIncidence.input_quadratic_slot out t g m).symm

/-- Signed-label specialization commutes with every coefficient-field extension. -/
theorem extended_signed_labels {k L : Type*} [Field k] [Field L] (φ : k →+* L)
    (a : I → Option J → kˣ) (t : RatioParameters I J) :
    ratioParameterValues (TorusCritical.mapUnits φ a) t = φ (ratioParameterValues a t) := by
  rcases t with ⟨⟨i,j⟩,b⟩
  cases b <;> simp [ratioParameterValues,TorusCritical.mapUnits]

end
end PlanarUnitDistances.IntegralGrid
