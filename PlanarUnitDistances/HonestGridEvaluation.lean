import PlanarUnitDistances.HonestGridInput
import PlanarUnitDistances.PolynomialCoordinateSlice

namespace PlanarUnitDistances.IntegralGrid
open MvPolynomial
open TorusCritical (Coord Equation RatioParameters ratioParameterValues)
noncomputable section

variable {U V E k : Type*} {q : ℕ} [Field k]
abbrev FrozenField (k : Type*) [Field k] {V : Type*} (S : Set V) := FractionRing (MvPolynomial S k)

def inputScalar (S : Set V) : k →+* FrozenField k S :=
  (algebraMap (MvPolynomial S k) (FrozenField k S)).comp C

def honestValue (S : Set V) (u : U → k) (m : Fin q → FrozenField k S) :
    Honest q S U → FrozenField k S :=
  Sum.elim (Sum.elim m (fun s => algebraMap _ _ (X s : MvPolynomial S k))) ((inputScalar S) ∘ u)

def numbered (S : Set V) (free : (↑Sᶜ) ≃ Fin q) :
    MvPolynomial V k →+* MvPolynomial (Fin q) (FrozenField k S) :=
  (renameEquiv (FrozenField k S) free).toRingHom.comp (CoordinateSlice.specialize k S)

private def unpack {A B L : Type*} [CommRing L] (b : B → L) :
    Labels (A ⊕ B) →+* MvPolynomial A L :=
  eval₂Hom (C.comp (Int.castRingHom L)) (Sum.elim X (fun i => C (b i)))

private theorem eval_packed {A B L : Type*} [CommRing L] (b : B → L) (p : Labels (A ⊕ B)) :
    MvPolynomial.map (eval₂Hom (Int.castRingHom L) b) (sumAlgEquiv ℤ A B p) = unpack b p := by
  let φ := (MvPolynomial.map (σ:=A) (eval₂Hom (Int.castRingHom L) b)).comp (sumAlgEquiv ℤ A B).toRingHom
  have eq : φ=unpack b := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [φ,unpack]
    · rintro (x|y) <;> simp [φ,unpack]
  exact DFunLike.congr_fun eq p

private theorem state_evaluation (S : Set V) (free : (↑Sᶜ) ≃ Fin q) (u : U → k)
    (m : Fin q → FrozenField k S) (p : InStates U V) :
    unpack (honestValue S u m) (rename (role S free) (flatten p)) =
      numbered S free (MvPolynomial.map (eval₂Hom (Int.castRingHom k) u) p) := by
  classical
  let φ := (unpack (honestValue S u m)).comp ((rename (role S free)).toRingHom.comp flatten)
  let ψ := (numbered (k:=k) S free).comp (MvPolynomial.map (eval₂Hom (Int.castRingHom k) u))
  have eq : φ=ψ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      let lhs : Labels U →+* MvPolynomial (Fin q) (FrozenField k S) := φ.comp C
      let rhs : Labels U →+* MvPolynomial (Fin q) (FrozenField k S) := ψ.comp C
      have heq : lhs=rhs := by
        apply MvPolynomial.ringHom_ext
        · intro z
          simp [lhs,rhs,φ,ψ,unpack,flatten,numbered,CoordinateSlice.specialize_C]
        · intro t
          simp [lhs,rhs,φ,ψ,unpack,flatten,role,honestValue,inputScalar,numbered,CoordinateSlice.specialize_C]
      exact DFunLike.congr_fun heq c
    · intro x
      by_cases h : x ∈ S
      · simp [φ,ψ,unpack,flatten,role,h,honestValue,numbered,
          CoordinateSlice.specialize_X_mem (k:=k) S (⟨x,h⟩ : S)]
      · simp [φ,ψ,unpack,flatten,role,h,honestValue,numbered,
          CoordinateSlice.specialize_X_compl (k:=k) S (⟨x,h⟩ : (↑Sᶜ))]
  exact DFunLike.congr_fun eq p

/-- The represented polynomial is the literal coefficient of the chosen
power-weighted row over the function field of the actual sliced coordinates. -/
theorem honest_entry_evaluation [Fintype E] (p : E → InStates U V)
    (S : Set V) (free : (↑Sᶜ) ≃ Fin q) (index : E → ℕ) (r : Fin q) (d : Fin q →₀ ℕ)
    (u : U → k) (m : Fin q → FrozenField k S) :
    eval₂Hom (Int.castRingHom (FrozenField k S)) (honestValue S u m) (honestEntry p S free index r d) =
    (∑ e, C (m r)^(index e)*numbered S free (MvPolynomial.map (eval₂Hom (Int.castRingHom k) u) (p e))).coeff d := by
  unfold honestEntry
  rw [← coeff_map,eval_packed]
  unfold honestRow
  rw [map_sum]
  apply congrArg (fun z : MvPolynomial (Fin q) (FrozenField k S) => z.coeff d)
  apply Finset.sum_congr rfl
  intro e _
  rw [map_mul,map_pow,state_evaluation]
  simp [unpack,honestValue]

/-- Specialization of the compressed row at the normalized actual units and
integer mixing parameters, with the precise selected incidence polynomials. -/
theorem honest_actual_evaluation {I J : Type*} [Fintype I] [Fintype J] {r : ℕ}
    (i : I) (j : Option J) (pick : Fin r → Equation I J) (a : I → Option J → kˣ)
    (S : Set (Slots I J r)) (free : (↑Sᶜ) ≃ Fin q) (index : Input I J r → ℕ)
    (row : Fin q) (d : Fin q →₀ ℕ) (m : Fin q → ℕ) :
    eval₂Hom (Int.castRingHom (FrozenField k S)) (honestValue S (ratioParameterValues a) (fun i => (m i : FrozenField k S)))
      (honestEntry (table i j pick) S free index row d) =
    (∑ e, (m row : MvPolynomial (Fin q) (FrozenField k S))^(index e) *
      numbered S free (CriticalLocus.incidenceEquation (TorusCritical.ratio a i j)
        ((TorusCritical.equation a) ∘ pick) id e)).coeff d := by
  rw [honest_entry_evaluation]
  simp_rw [show eval₂Hom (Int.castRingHom k) (ratioParameterValues a) = atLabels a from rfl,map_table,map_natCast]
end
end PlanarUnitDistances.IntegralGrid
