import PlanarUnitDistances.IntegerTupleDensity
import PlanarUnitDistances.SpecialFiberCoefficient
import PlanarUnitDistances.SliceCoefficientExtraction

namespace PlanarUnitDistances.StationaryDeformation
open MvPolynomial Filter UniversalIncidence
noncomputable section

/-- The first block is specialized at ordinary integers, the second is left
algebraically independent in the given injection of polynomial rings. -/
def mixedEvaluation {k S L : Type*} [Field k] [CommRing L] {q : ℕ}
    (ι : MvPolynomial S k →+* L) (a : Fin q → ℕ) :
    MvPolynomial (Fin q ⊕ S) k →+* L :=
  ι.comp ((eval (fun i => (a i : MvPolynomial S k))).comp (sumAlgEquiv k (Fin q) S).toRingHom)

@[simp] theorem mixedEvaluation_C {k S L : Type*} [Field k] [CommRing L] {q : ℕ}
    (ι : MvPolynomial S k →+* L) (a : Fin q → ℕ) (x : k) :
    mixedEvaluation ι a (C x) = ι (C x) := by simp [mixedEvaluation]

@[simp] theorem mixedEvaluation_mix {k S L : Type*} [Field k] [CommRing L] {q : ℕ}
    (ι : MvPolynomial S k →+* L) (a : Fin q → ℕ) (i : Fin q) :
    mixedEvaluation ι a (X (Sum.inl i)) = (a i : L) := by simp [mixedEvaluation]

@[simp] theorem mixedEvaluation_frozen {k S L : Type*} [Field k] [CommRing L] {q : ℕ}
    (ι : MvPolynomial S k →+* L) (a : Fin q → ℕ) (s : S) :
    mixedEvaluation ι a (X (Sum.inr s)) = ι (X s) := by simp [mixedEvaluation]

theorem mixedEvaluation_separates {k S L : Type*} [Field k] [CharZero k] [CommRing L] {q : ℕ}
    (ι : MvPolynomial S k →+* L) (inj : Function.Injective ι)
    (p : MvPolynomial (Fin q ⊕ S) k) (hp : p ≠ 0) :
    ∀ᶠ a in integerTuples q, mixedEvaluation ι a p ≠ 0 := by
  have nz := (map_ne_zero_iff _ (sumAlgEquiv k (Fin q) S).injective).mpr hp
  filter_upwards [eventually_integer_eval_ne_zero q _ nz] with a survives
  exact (map_ne_zero_iff ι inj).mpr survives

/-- For a fixed output c, the first surviving deformation coefficient at a
generic integer tuple vanishes at c. Select a single monomial in all auxiliary
variables to obtain a nonzero equation in k[T]. This selection costs no degree
or coefficient size: every coefficient is one specified old coefficient. -/
theorem descend_generic_first_root {k S L : Type} [Field k] [CharZero k] [CommRing L] {q : ℕ}
    (ι : MvPolynomial S k →+* L) (inj : Function.Injective ι) (c : k)
    (H : Polynomial (Polynomial (MvPolynomial (Fin q ⊕ S) k)))
    (root : ∀ᶠ a in integerTuples q, ∃ e,
      ((H.coeff e).map (mixedEvaluation ι a)) ≠ 0 ∧
      (∀ j < e, (H.coeff j).map (mixedEvaluation ι a) = 0) ∧
      ((H.coeff e).map (mixedEvaluation ι a)).IsRoot (ι (C c))) :
    ∃ d m, parameterCoefficient (H.coeff d) m ≠ 0 ∧
      (parameterCoefficient (H.coeff d) m).IsRoot c := by
  classical
  have nz : H ≠ 0 := by
    obtain ⟨a,e,survives,_⟩ := root.exists
    rintro rfl
    exact survives (by simp)
  obtain ⟨d,hd,before,_⟩ := first_surviving_coefficient H nz
  have someCoefficient : ∃ j, (H.coeff d).coeff j ≠ 0 := by
    by_contra! zero
    exact hd (Polynomial.ext (by simpa using zero))
  obtain ⟨j,hj⟩ := someCoefficient
  have vanish : (H.coeff d).eval (C c) = 0 := by
    by_contra wrong
    have absurdly : ∀ᶠ _ in integerTuples q, False := by
      filter_upwards [root, mixedEvaluation_separates ι inj _ hj,
        mixedEvaluation_separates ι inj _ wrong] with a chosen persists nonzero
      obtain ⟨e,he,earlier,atRoot⟩ := chosen
      have hd' : (H.coeff d).map (mixedEvaluation ι a) ≠ 0 := by
        intro z
        apply persists
        simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using
          congrArg (fun f : Polynomial L => f.coeff j) z
      have equal : e = d := le_antisymm
        (le_of_not_gt (fun lt => hd' (earlier d lt)))
        (le_of_not_gt (fun lt => he (by simp [before e lt])))
      subst e
      apply nonzero
      rw [← Polynomial.eval₂_hom, ← Polynomial.eval_map, mixedEvaluation_C]
      exact atRoot
    exact absurdly.exists.choose_spec
  obtain ⟨m,hm,roots⟩ := extract_base_field_polynomial (H.coeff d) hd (RingHom.id _) Function.injective_id
  exact ⟨d,m,hm,roots c (by simpa [Polynomial.IsRoot] using vanish)⟩

end
end PlanarUnitDistances.StationaryDeformation
