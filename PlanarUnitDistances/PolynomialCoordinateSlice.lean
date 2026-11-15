import PlanarUnitDistances.CoordinateSlice

namespace PlanarUnitDistances.CoordinateSlice
open MvPolynomial Set
noncomputable section
variable {k V : Type*} [Field k]

abbrev SliceRing (k : Type*) [Field k] {V : Type*} (S : Set V) :=
  MvPolynomial (↑Sᶜ) (FractionRing (Poly k S))

def split (k : Type*) [Field k] {V : Type*} (S : Set V) :
    Poly k V ≃ₐ[k] MvPolynomial (↑Sᶜ) (Poly k S) := by
  classical
  exact (renameEquiv k ((Equiv.Set.sumCompl S).symm.trans (Equiv.sumComm _ _))).trans (sumAlgEquiv k _ _)

@[simp] theorem split_X_mem (S : Set V) (i : S) : split k S (X i.1) = C (X i) := by
  classical
  simp [split]

@[simp] theorem split_X_compl (S : Set V) (i : (↑Sᶜ)) : split k S (X i.1) = X i := by
  classical
  simp [split]

@[simp] theorem split_rename (S : Set V) (f : Poly k S) :
    split k S (rename ((↑) : S → V) f) = C f := by
  have h : (split k S).toAlgHom.comp (rename ((↑) : S → V)) =
      IsScalarTower.toAlgHom k (Poly k S) (MvPolynomial (↑Sᶜ) (Poly k S)) := by
    ext i
    simp [IsScalarTower.toAlgHom_apply]
  exact DFunLike.congr_fun h f

/-- Move the basis variables into the rational-function coefficient field,
leaving the complementary coordinates as genuinely independent polynomial variables. -/
def specialize (k : Type*) [Field k] {V : Type*} (S : Set V) : Poly k V →+* SliceRing k S :=
  (MvPolynomial.map (algebraMap (Poly k S) (FractionRing (Poly k S)))).comp (split k S).toRingHom

@[simp] theorem specialize_X_mem (S : Set V) (i : S) :
    specialize k S (X i.1) = C (algebraMap (Poly k S) (FractionRing (Poly k S)) (X i)) := by
  simp [specialize]

@[simp] theorem specialize_X_compl (S : Set V) (i : (↑Sᶜ)) :
    specialize k S (X i.1) = X i := by simp [specialize]

@[simp] theorem specialize_C (S : Set V) (c : k) :
    specialize k S (C c) = C (algebraMap (Poly k S) (FractionRing (Poly k S)) (C c)) := by
  simp [specialize,split]

attribute [local instance] algebraMvPolynomial

/-- The polynomial ring on the remaining variables is exactly the localization
of the original ring at nonzero polynomials in the chosen coordinate variables. -/
theorem specialize_isLocalization (S : Set V) :
    letI := (specialize k S).toAlgebra
    IsLocalization (denominators k S) (SliceRing k S) := by
  letI := (specialize k S).toAlgebra
  let M := (nonZeroDivisors (Poly k S)).map (C (σ := (↑Sᶜ)))
  apply IsLocalization.of_ringEquiv_left (M₁ := M) (split k S).toRingEquiv _ (fun _ => rfl)
  ext x
  constructor
  · rintro ⟨_,⟨f,hf,rfl⟩,rfl⟩
    exact ⟨f,hf,(split_rename S f).symm⟩
  · rintro ⟨f,hf,rfl⟩
    exact ⟨_,⟨f,hf,rfl⟩,split_rename S f⟩

/-- A constant output coordinate cannot be part of the transcendence basis. -/
theorem constant_not_basis {P : Ideal (Poly k V)} [P.IsPrime] {S : Set V}
    (basis : IsTranscendenceBasis k (fun i : S => residue P i.1)) {o : V} {c : k}
    (value : X o-C c ∈ P) : o ∉ S := by
  intro hs
  have e : residue P o = algebraMap k (Poly k V ⧸ P) c := by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr value
    have eq : Ideal.Quotient.mk P (X o) = Ideal.Quotient.mk P (C c) := by
      simpa only [map_sub,sub_eq_zero] using this
    exact eq.trans (by simpa only [MvPolynomial.algebraMap_eq] using Ideal.Quotient.mk_algebraMap k P c)
  apply basis.1.transcendental (⟨o,hs⟩ : S)
  change IsAlgebraic k (residue P o)
  rw [e]
  exact isAlgebraic_algebraMap c

/-- After selection, the prescribed component is both isolated and a closed
point of the polynomial system over the rational-function field. -/
theorem polynomial_coordinate_slice {I P : Ideal (Poly k V)} (hP : P ∈ I.minimalPrimes)
    (o : V) (c : k) (value : X o-C c ∈ P) :
    ∃ (S : Set V) (ho : o ∉ S), IsTranscendenceBasis k (fun i : S => residue P i.1) ∧
      ∃ Q : Ideal (SliceRing k S), Q.IsMaximal ∧ Q ∈ (I.map (specialize k S)).minimalPrimes ∧
        Q.comap (specialize k S)=P ∧
        X (⟨o,ho⟩ : (↑Sᶜ))-C (algebraMap (Poly k S) (FractionRing (Poly k S)) (C c)) ∈ Q := by
  letI := hP.isPrime
  obtain ⟨S,basis⟩ := coordinate_basis P
  have ho := constant_not_basis basis value
  letI := (specialize k S).toAlgebra
  letI := specialize_isLocalization (k:=k) S
  obtain ⟨maximal,minimum,under⟩ := slice_at_basis hP basis (SliceRing k S)
  refine ⟨S,ho,basis,P.map (specialize k S),maximal,minimum,under,?_⟩
  have mem := Ideal.mem_map_of_mem (specialize k S) value
  simpa only [map_sub,specialize_C,specialize_X_compl (k:=k) S (⟨o,ho⟩ : (↑Sᶜ))] using mem

end
end PlanarUnitDistances.CoordinateSlice
