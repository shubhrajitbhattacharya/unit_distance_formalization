import PlanarUnitDistances.HonestMacaulayTable
import PlanarUnitDistances.NumberedCoordinateSlice

namespace PlanarUnitDistances.IntegralGrid
open MvPolynomial CriticalLocus HomogeneousMacaulay UniversalIncidence
open TorusCritical (Equation ratioParameterValues)
noncomputable section
variable {I J k : Type*} [Fintype I] [Fintype J] [Field k] {r q w : ℕ}

abbrev outputSlot (I J : Type*) (r : ℕ) : Slots I J r := .inr (.inr ())

/-- With the exact equation order used by the generic square selection,
the inspected slots are precisely its homogenized mixed rows and its actual
surviving output coordinate. -/
theorem actual_numbered_homogeneous_table (a : I → Option J → kˣ)
    (i : I) (j : Option J) (pick : Fin r → Equation I J)
    (S : Set (Slots I J r)) (free : (↑Sᶜ) ≃ Fin q)
    (ho : outputSlot I J r ∉ S) (ord : Input I J r ≃ Fin w) (mix : Fin q → ℕ) :
    let out := free ⟨outputSlot I J r,ho⟩
    let equations (e : Fin w) := incidenceEquation (TorusCritical.ratio a i j)
      ((TorusCritical.equation a) ∘ pick) id (ord.symm e)
    let g t := StationaryDeformation.combination (fun e => CoordinateSlice.numbered k S free (equations e)) (mix t)
    ∀ b m, eval₂Hom (Int.castRingHom (FrozenField k S))
       (honestValue S (ratioParameterValues a) (fun t => (mix t : FrozenField k S)))
       (honestCoefficients i j pick S free ord out b m) =
      inputCoefficients out (fun t => quadraticHomogenization (g t)) b m := by
  intro out equations g
  have h (t : Fin q) : (∑ e, (mix t : MvPolynomial (Fin q) (FrozenField k S)) ^ (ord e).val *
      numbered S free (incidenceEquation (TorusCritical.ratio a i j)
        ((TorusCritical.equation a) ∘ pick) id e)) = g t := by
    let term (u : Fin w) := (mix t : MvPolynomial (Fin q) (FrozenField k S))^u.val *
      CoordinateSlice.numbered k S free (equations u)
    have he := ord.sum_comp term
    simpa only [term,equations,g,StationaryDeformation.combination,Equiv.symm_apply_apply,numbered,CoordinateSlice.numbered] using he
  intro b m
  exact (honest_coefficients_evaluation a i j pick S free ord out mix b m).trans (by simp_rw [h])

end
end PlanarUnitDistances.IntegralGrid
