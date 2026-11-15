import PlanarUnitDistances.GenericRootDescent
import PlanarUnitDistances.QuadraticHomogenization
import PlanarUnitDistances.SpecializedCoefficientBudget
import PlanarUnitDistances.IntegerCoordinateSplit

namespace PlanarUnitDistances.StationaryDeformation
open MvPolynomial UniversalIncidence HomogeneousMacaulay BlockMacaulay
open MacaulayFactorBounds EliminantHeight
noncomputable section

/-- Keep all auxiliary variables independent while specializing the actual label values. -/
def specializeLabels {U V k : Type*} [Field k] (x : U → k) :
    MvPolynomial (V ⊕ U) ℤ →+* MvPolynomial V k :=
  (MvPolynomial.map (aeval (R:=ℤ) x).toRingHom).comp (sumAlgEquiv ℤ V U).toRingHom

theorem coefficient_specializeLabels {U V k : Type*} [Field k] (x : U → k)
    (p : MvPolynomial (V ⊕ U) ℤ) (m : V →₀ ℕ) :
    (specializeLabels x p).coeff m = aeval x ((sumAlgEquiv ℤ V U p).coeff m) := by
  simp [specializeLabels,MvPolynomial.coeff_map]

/-- Compute one swapped, deformed coefficient either before or after specializing
all integral inputs. No scalar division or degree-preserving assumption is used. -/
theorem mapped_swapped_coeff {q : ℕ} {R D : Type*} [CommRing R] [CommRing D]
    (f : R →+* D) (A : Coefficients q R) (F : Universal q) (e : ℕ) :
    ((Polynomial.Bivariate.swap (deformationMap A F)).coeff e).map f =
      (Polynomial.Bivariate.swap (deformationMap (fun i m => f (A i m)) F)).coeff e := by
  apply Polynomial.ext
  intro t
  rw [Polynomial.coeff_map,swap_coeff_coeff,swap_coeff_coeff,←map_deformation f A F,
    Polynomial.coeff_map]
  exact (Polynomial.coeff_map f _).symm

/-- On the isolated component, all auxiliary choices disappear from the height
estimate. The input table is integral before specializing the labels, the
frozen coordinates or the integer row combinations. The field L holding the
component need not be a number field or be algebraic over k. -/
theorem bounded_generic_root {k L U S : Type} [Field k] [CharZero k] [Field L]
    [Fintype U] [Fintype S] {q : ℕ} (hq : q ≤ 98)
    (x : U → k) (ι : MvPolynomial S k →+* L) (injective : Function.Injective ι)
    (c : k) (j : Fin q) (M : Ideal (State q L)) [M.IsMaximal]
    (value : X j - C (ι (C c)) ∈ M)
    (g : (Fin q → ℕ) → Fin q → State q L)
    (deg : ∀ a i, (g a i).totalDegree ≤ 2)
    (isolated : ∀ᶠ a in integerTuples q, M ∈ (Ideal.span (Set.range (g a))).minimalPrimes)
    (A : Coefficients q (MvPolynomial ((Fin q ⊕ S) ⊕ U) ℤ))
    (degreeA : ∀ i m, (A i m).totalDegree ≤ 256)
    (sizeA : ∀ i m, coefficientSum (A i m) ≤ 2^200)
    (entries : ∀ a i m, mixedEvaluation ι a (specializeLabels x (A i m)) =
      inputCoefficients j (fun t => quadraticHomogenization (g a t)) i m) :
    ∃ p : Polynomial k, p ≠ 0 ∧ p.IsRoot c ∧
      ∀ t, ∃ G : MvPolynomial U ℤ, G.totalDegree ≤ 2^112 ∧
        coefficientSum G ≤ 2^(2^402) ∧ p.coeff t = aeval x G := by
  classical
  obtain ⟨F,_,rel,ker,_⟩ := exists_bounded_incidence_relation q hq
  have divides (i : Coord q) : F ∣ minor i := (ker _).mp (minor_in_kernel i)
  let B := fun i m => specializeLabels x (A i m)
  let H := Polynomial.Bivariate.swap (deformationMap B F)
  have generic : ∀ᶠ a in integerTuples q, ∃ e,
      ((H.coeff e).map (mixedEvaluation ι a)) ≠ 0 ∧
      (∀ t < e, (H.coeff t).map (mixedEvaluation ι a) = 0) ∧
      ((H.coeff e).map (mixedEvaluation ι a)).IsRoot (ι (C c)) := by
    filter_upwards [isolated] with a good
    have same : (fun i m => mixedEvaluation ι a (B i m)) =
        inputCoefficients j (fun t => quadraticHomogenization (g a t)) := funext fun i => funext (entries a i)
    obtain ⟨_,e,ne,first,roots⟩ := affine_coordinate_from_relation F rel
      ((ker _).mp original_determinant_in_kernel) L j (g a) (deg a)
    simp only [H,mapped_swapped_coeff,same]
    exact ⟨e,ne,first,(roots M good).2 _ value⟩
  obtain ⟨d,m,nz,root⟩ := descend_generic_first_root ι injective c H generic
  refine ⟨parameterCoefficient (H.coeff d) m,nz,root,?_⟩
  intro t
  let P := ((Polynomial.Bivariate.swap (deformationMap A F)).coeff d).coeff t
  let G := ((sumAlgEquiv ℤ (Fin q ⊕ S) U) P).coeff m
  obtain ⟨dp,sp⟩ := specialized_coefficient_budget hq F divides A degreeA sizeA t d
  refine ⟨G,(IntegralCoordinateSplit.sum_coeff_degree P m).trans dp,
    (IntegralCoordinateSplit.sum_coeff_bound P m).trans sp,?_⟩
  rw [parameterCoefficient_coeff]
  dsimp only [H,B]
  rw [←mapped_swapped_coeff (specializeLabels x) A F d,Polynomial.coeff_map]
  exact coefficient_specializeLabels x P m

end
end PlanarUnitDistances.StationaryDeformation
