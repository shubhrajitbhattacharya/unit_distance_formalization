import PlanarUnitDistances.GenericRootDescent
import PlanarUnitDistances.HonestGridEvaluation

namespace PlanarUnitDistances.IntegralGrid
open MvPolynomial StationaryDeformation
noncomputable section
variable {k L U V : Type*} [Field k] [Field L] {q : ℕ}

/-- Embed the source-field polynomial ring on the actual frozen coordinates
into the rational function field over the ambient coefficient field. -/
def embedFrozen (φ : k →+* L) (S : Set V) : MvPolynomial S k →+* FrozenField L S :=
  (algebraMap (MvPolynomial S L) (FrozenField L S)).comp (MvPolynomial.map φ)

theorem embedFrozen_injective (φ : k →+* L) (S : Set V) : Function.Injective (embedFrozen φ S) :=
  (IsFractionRing.injective (MvPolynomial S L) (FrozenField L S)).comp (map_injective φ φ.injective)

@[simp] theorem embedFrozen_C (φ : k →+* L) (S : Set V) (c : k) :
    embedFrozen φ S (C c) = algebraMap (MvPolynomial S L) (FrozenField L S) (C (φ c)) := by
  simp [embedFrozen]

@[simp] theorem embedFrozen_X (φ : k →+* L) (S : Set V) (s : S) :
    embedFrozen φ S (X s) = algebraMap (MvPolynomial S L) (FrozenField L S) (X s) := by
  simp [embedFrozen]

/-- On the integral table, specializing the source-field labels and then
specializing the integer row choices agrees with the direct evaluation in
the ambient rational function field; the frozen coordinates stay independent.
The second homomorphism on the left is the definition of `specializeLabels`. -/
theorem mixedEvaluation_eq_honest (φ : k →+* L) (S : Set V) (u : U → k) (a : Fin q → ℕ) :
    (mixedEvaluation (embedFrozen φ S) a).comp
      ((MvPolynomial.map (aeval (R:=ℤ) u).toRingHom).comp (sumAlgEquiv ℤ (Fin q ⊕ S) U).toRingHom) =
    eval₂Hom (Int.castRingHom (FrozenField L S))
      (honestValue S (φ ∘ u) (fun i => (a i : FrozenField L S))) := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [honestValue,inputScalar]
  · rintro ((i|s)|t) <;> simp [honestValue,inputScalar]

end
end PlanarUnitDistances.IntegralGrid
