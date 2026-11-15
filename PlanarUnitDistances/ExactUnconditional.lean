import PlanarUnitDistances.NumberedStationaryRows
import PlanarUnitDistances.HonestNumberedTable
import PlanarUnitDistances.MixedHonestEvaluation
import PlanarUnitDistances.BoundedGenericRoot
import PlanarUnitDistances.HeightFromCoefficientForms
import PlanarUnitDistances.ExactFromAffineStationary

namespace PlanarUnitDistances.IntegralGrid
open CriticalLocus MvPolynomial StationaryDeformation TorusCritical
noncomputable section

/-- The chosen component of the literal normalized stationary grid determines
a nonzero polynomial of controlled coefficient height over the original number
field, even if the component is defined only over the complex numbers. -/
theorem stationary_height_unconditional :
    ResearchMotion.LocalizedGridWithCap (fun s => (2:ℝ)^2086+(2:ℝ)^113*s) := by
  intro K _ _ _ I J _ _ r a i j _row _col _mi _ma _lj _hj hr pick c P hP hc hq
  classical
  let φ := algebraMap K ℂ
  let α := mapUnits φ a
  let ord := Fintype.equivFin (Input I J r)
  let eqs := orderedOriginal α i j pick ord
  let o := outputSlot I J r
  letI := hP.isPrime
  obtain ⟨Q,hQ,_QP,hcQ⟩ := constant_on_selected_component
    (TorusCritical.ratio α i j) (TorusCritical.equation α) pick P hP.le (φ c) hc
  have selected : Q ∈ (Ideal.span (Set.range eqs)).minimalPrimes := by
    simpa only [eqs,span_orderedOriginal] using hQ
  have valued : X o-C (φ c) ∈ Q := hcQ
  obtain ⟨S,ho,_basis,q,free,_qcard,qle,M,hM,hmin,_contract,constant,degree⟩ :=
    CoordinateSlice.numbered_coordinate_slice eqs Q selected o (φ c) valued
      (orderedOriginal_degree α i j pick ord)
  letI := hM
  letI : Fintype S := Fintype.ofFinite S
  let out := free (⟨o,ho⟩ : (↑Sᶜ))
  let G := fun t => CoordinateSlice.numbered ℂ S free (eqs t)
  let g (a : Fin q → ℕ) (t : Fin q) := combination G (a t)
  let A := honestCoefficients i j pick S free ord out
  have budget (b m) := honest_coefficients_budget i j pick hr hq S free ord out b m
  have qsmall : q≤98 := qle.trans (by simpa only [Nat.card_eq_fintype_card] using hq)
  have root_value : X out-C ((embedFrozen φ S) (C c)) ∈ M := by
    simpa only [embedFrozen_C] using constant
  have labels : φ ∘ ratioParameterValues a = ratioParameterValues α :=
    funext fun t => (extended_signed_labels φ a t).symm
  obtain ⟨p,hp,root,forms⟩ := bounded_generic_root qsmall (ratioParameterValues a)
    (embedFrozen φ S) (embedFrozen_injective φ S) c out M root_value g
    (fun mix t => combination_degree G degree (mix t))
    (CoordinateSlice.eventual_square_after_slice S free eqs M hmin) A
    (fun b m => (budget b m).1.trans (by decide))
    (fun b m => (budget b m).2.trans (Nat.pow_le_pow_right (by decide) (by decide : 173≤200)))
    (by
      intro mix b m
      have ev := DFunLike.congr_fun (mixedEvaluation_eq_honest φ S (ratioParameterValues a) mix) (A b m)
      rw [labels] at ev
      exact ev.trans (actual_numbered_homogeneous_table α i j pick S free ho ord mix b m))
  exact ratio_height_from_bounded_coefficient_forms a c p hp root (fun t => forms t.val)

/-- The manuscript's exact Theorem A, for unrestricted planar configurations. -/
theorem exact_unconditional : TheoremA :=
  ResearchPhysical.exact_from_affine_stationary_heights (le_refl _) (le_refl _) stationary_height_unconditional

end
end PlanarUnitDistances.IntegralGrid
