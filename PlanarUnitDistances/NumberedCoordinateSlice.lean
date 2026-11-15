import PlanarUnitDistances.PolynomialSliceDegree
import PlanarUnitDistances.GenericSquareSelection
import PlanarUnitDistances.MaximalPolynomialHeight

namespace PlanarUnitDistances.CoordinateSlice
open MvPolynomial Set Filter
noncomputable section
variable {k V : Type*} [Field k]

abbrev FrozenField (k : Type*) [Field k] {V : Type*} (S : Set V) := FractionRing (Poly k S)

def numbered (k : Type*) [Field k] {V : Type*} (S : Set V) {q : ℕ} (e : (↑Sᶜ) ≃ Fin q) :
    Poly k V →+* MvPolynomial (Fin q) (FrozenField k S) :=
  (renameEquiv (FrozenField k S) e).toRingHom.comp (specialize k S)


@[simp] theorem numbered_X_compl (S : Set V) {q : ℕ} (e : (↑Sᶜ) ≃ Fin q) (v : (↑Sᶜ)) :
    numbered k S e (X v.1)=X (e v) := by simp [numbered]

@[simp] theorem numbered_C (S : Set V) {q : ℕ} (e : (↑Sᶜ) ≃ Fin q) (c : k) :
    numbered k S e (C c)=C (algebraMap (Poly k S) (FrozenField k S) (C c)) := by
  simp [numbered]

theorem numbered_totalDegree (S : Set V) {q : ℕ} (e : (↑Sᶜ) ≃ Fin q) (p : Poly k V) :
    (numbered k S e p).totalDegree≤p.totalDegree :=
  (totalDegree_rename_le e _).trans (specialize_totalDegree S p)

set_option maxHeartbeats 600000 in
/-- Freeze exactly a coordinate transcendence basis for the selected
component and number the complementary coordinates. The given output
coordinate survives, and the new isolated maximal prime contracts back
to the specified original component. No algebraic-closure change is used. -/
theorem numbered_coordinate_slice [Finite V] {w : ℕ} (g : Fin w → Poly k V)
    (P : Ideal (Poly k V)) (component : P ∈ (Ideal.span (range g)).minimalPrimes)
    (o : V) (c : k) (value : X o-C c∈P) (degree : ∀t,(g t).totalDegree≤2) :
    ∃ (S : Set V) (ho : o ∉ S), IsTranscendenceBasis k (fun i : S => residue P i.1) ∧
      ∃ (q : ℕ) (e : (↑Sᶜ) ≃ Fin q), q=Nat.card (↑Sᶜ) ∧ q≤Nat.card V ∧
        let j := e (⟨o,ho⟩ : (↑Sᶜ))
        let G := fun t => numbered k S e (g t)
        ∃ M : Ideal (MvPolynomial (Fin q) (FrozenField k S)), M.IsMaximal ∧
          M ∈ (Ideal.span (range G)).minimalPrimes ∧ M.comap (numbered k S e)=P ∧
          X j-C (algebraMap (Poly k S) (FrozenField k S) (C c))∈M ∧ ∀t,(G t).totalDegree≤2 := by
  classical
  obtain ⟨S,ho,basis,Q,maxQ,minQ,under,root⟩ := polynomial_coordinate_slice component o c value
  let q := Nat.card (↑Sᶜ)
  let e := Finite.equivFin (↑Sᶜ)
  let E := (renameEquiv (FrozenField k S) e).toRingEquiv
  let f : SliceRing k S →+* MvPolynomial (Fin q) (FrozenField k S) := E.toRingHom
  let G := fun t => numbered k S e (g t)
  let I := Ideal.span (range g)
  have mapped : (I.map (specialize k S)).map f=Ideal.span (range G) := by
    change ((Ideal.span (range g)).map (specialize k S)).map f=_
    rw [Ideal.map_span,Ideal.map_span,←Set.range_comp,←Set.range_comp]
    rfl
  let _ : Q.IsMaximal := maxQ
  have maxM : (Q.map f).IsMaximal := Ideal.map_isMaximal_of_equiv E
  have ker : RingHom.ker f=⊥ := (RingHom.injective_iff_ker_eq_bot f).mp E.injective
  have minM : Q.map f ∈ (Ideal.span (range G)).minimalPrimes := by
    rw [←mapped,Ideal.minimalPrimes_map_of_surjective (f:=f) E.surjective,ker,sup_bot_eq]
    exact ⟨Q,minQ,rfl⟩
  have back : (Q.map f).comap f=Q := by
    rw [Ideal.comap_map_of_surjective f E.surjective]
    change Q ⊔ RingHom.ker f = Q
    rw [ker,sup_bot_eq]
  have contract : (Q.map f).comap (numbered k S e)=P := by
    change (Q.map f).comap (f.comp (specialize k S))=P
    rw [←Ideal.comap_comap,back,under]
  refine ⟨S,ho,basis,q,e,rfl,Nat.card_le_card_of_injective ((↑) : (↑Sᶜ) → V) Subtype.val_injective,
    Q.map f,maxM,minM,contract,?_,fun t => (numbered_totalDegree _ _ _).trans (degree t)⟩
  have h : X o-C c ∈ (Q.map f).comap (numbered k S e) := contract.symm ▸ value
  change numbered k S e (X o-C c) ∈ Q.map f at h
  rw [map_sub, numbered_C, numbered_X_compl S e (⟨o,ho⟩ : (↑Sᶜ))] at h
  exact h

/-- Over characteristic zero the very ideal produced above admits q
explicit Vandermonde combinations for nested cofinally many choices. -/
theorem eventual_square_after_slice [CharZero k] (S : Set V) {q w : ℕ} (e : (↑Sᶜ) ≃ Fin q)
    (g : Fin w → Poly k V) (M : Ideal (MvPolynomial (Fin q) (FrozenField k S))) [M.IsMaximal]
    (isolated : M ∈ (Ideal.span (range (fun t => numbered k S e (g t)))).minimalPrimes) :
    ∀ᶠ a in StationaryDeformation.integerTuples q, M ∈ (Ideal.span (range
      (fun i => StationaryDeformation.combination (fun t => numbered k S e (g t)) (a i)))).minimalPrimes :=
  StationaryDeformation.generic_square_selection (k:=FrozenField k S) _ M isolated q
    (StationaryDeformation.maximal_height_fin q M)

end
end PlanarUnitDistances.CoordinateSlice
