import PlanarUnitDistances.QuadraticRadicals

/- Adapted from OpenAI math, UnitDistances/Valuations.lean, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, Apache-2.0. -/

namespace OAI

namespace PlanarUnitDistances.Radicals

universe u v

open WithZero Multiplicative

theorem exp_neg_one_ne_square (x : ℤᵐ⁰) : WithZero.exp (-1 : ℤ) ≠ x ^ 2 := by
  intro h
  have h' := congrArg WithZero.log h
  simp only [WithZero.log_exp, WithZero.log_pow, nsmul_eq_mul] at h'
  omega

theorem squareIndependent_of_private_valuations
    {K : Type u} [Field K] {ι : Type v} (is : List ι) (hi : is.Nodup)
    (d : ι → K)
    (hv : ∀ i ∈ is, ∃ v : Valuation K ℤᵐ⁰,
      v (d i) = WithZero.exp (-1 : ℤ) ∧ ∀ j ∈ is, j ≠ i → v (d j) = 1) :
    SquareIndependent (is.map d) := by
  intro s hs hsn c hc
  obtain ⟨js, hj, rfl⟩ := List.sublist_map_iff.mp hs
  cases js with
  | nil => exact hsn rfl
  | cons i js =>
    have hnd := List.nodup_cons.mp (hi.sublist hj)
    have him : i ∈ is := hj.subset (by simp)
    obtain ⟨v, hvi, hvj⟩ := hv i him
    have hone : (js.map (fun j => v (d j))).prod = 1 := by
      apply List.prod_eq_one
      intro a ha
      obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp ha
      exact hvj j (hj.subset (by simp [hjm])) (by
        intro he; exact hnd.1 (he ▸ hjm))
    apply exp_neg_one_ne_square (v c)
    have hh := congrArg v hc
    simpa [map_list_prod, List.map_map, Function.comp_def, hvi, hone] using hh

section RootValuation

open Polynomial IsDedekindDomain

variable {K : Type u} [Field K]

noncomputable def pointPrime (a : K) : HeightOneSpectrum K[X] where
  asIdeal := Ideal.span {X - C a}
  isPrime := by
    rw [Ideal.span_singleton_prime (X_sub_C_ne_zero a)]
    exact prime_X_sub_C a
  ne_bot := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact X_sub_C_ne_zero a

noncomputable def pointValuation (a : K) : Valuation (RatFunc K) ℤᵐ⁰ :=
  (pointPrime a).valuation (RatFunc K)

theorem pointValuation_polynomial_of_eval_ne_zero {a : K} {p : K[X]}
    (hp : p.eval a ≠ 0) :
    pointValuation a (algebraMap K[X] (RatFunc K) p) = 1 := by
  apply (HeightOneSpectrum.valuation_eq_one_iff_notMem (pointPrime a)).mpr
  simpa [pointPrime, Ideal.mem_span_singleton, dvd_iff_isRoot, IsRoot] using hp

theorem pointValuation_X_sub_C (a : K) :
    pointValuation a (algebraMap K[X] (RatFunc K) (X - C a)) =
      WithZero.exp (-1 : ℤ) := by
  rw [pointValuation, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton (pointPrime a) (X_sub_C_ne_zero a) rfl

theorem pointValuation_of_simple_root {a : K} {p : K[X]}
    (hp : p.eval a = 0) (hp' : p.derivative.eval a ≠ 0) :
    pointValuation a (algebraMap K[X] (RatFunc K) p) =
      WithZero.exp (-1 : ℤ) := by
  obtain ⟨q, hq⟩ := (dvd_iff_isRoot.mpr hp : X - C a ∣ p)
  have hq' : q.eval a ≠ 0 := by
    simpa [hq, derivative_mul] using hp'
  rw [hq, map_mul, map_mul, pointValuation_X_sub_C,
    pointValuation_polynomial_of_eval_ne_zero hq', mul_one]

theorem squareIndependent_of_private_simple_roots {ι : Type v}
    (is : List ι) (hi : is.Nodup) (d : ι → K[X])
    (h : ∀ i ∈ is, ∃ a : K, (d i).eval a = 0 ∧
      (d i).derivative.eval a ≠ 0 ∧ ∀ j ∈ is, j ≠ i → (d j).eval a ≠ 0) :
    SquareIndependent (is.map (fun i => algebraMap K[X] (RatFunc K) (d i))) := by
  apply squareIndependent_of_private_valuations is hi
  intro i him
  obtain ⟨a, hai, hai', haj⟩ := h i him
  exact ⟨pointValuation a, pointValuation_of_simple_root hai hai',
    fun j hj hji => pointValuation_polynomial_of_eval_ne_zero (haj j hj hji)⟩

end RootValuation

section Plane

open Polynomial

variable {K : Type u} [Field K] [CharZero K]

omit [CharZero K] in
lemma ratFunc_X_sub_C_ne_zero (a : K) :
    (RatFunc.X : RatFunc K) - RatFunc.C a ≠ 0 := by
  simpa using RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a)

noncomputable def planePrivateRoot (a b : K) : RatFunc K :=
  (RatFunc.C b * (RatFunc.X - RatFunc.C a) + 4) /
    (RatFunc.X - RatFunc.C a)

lemma planePrivateRoot_ne_constant (a b c : K) :
    planePrivateRoot a b ≠ RatFunc.C c := by
  intro h
  have he := (div_eq_iff (ratFunc_X_sub_C_ne_zero a)).mp h
  have hp : C b * (X - C a) + 4 = C c * (X - C a) := by
    apply RatFunc.algebraMap_injective K
    simpa only [map_mul, map_sub, map_add, map_ofNat, RatFunc.algebraMap_C,
      RatFunc.algebraMap_X] using he
  have hp' := congrArg (Polynomial.eval a) hp
  norm_num at hp'

lemma planePrivateRoot_injective :
    Function.Injective (fun ab : K × K => planePrivateRoot ab.1 ab.2) := by
  intro ab cd he
  change planePrivateRoot ab.1 ab.2 = planePrivateRoot cd.1 cd.2 at he
  have hc := (div_eq_div_iff (ratFunc_X_sub_C_ne_zero ab.1)
    (ratFunc_X_sub_C_ne_zero cd.1)).mp he
  have hp : (C ab.2 * (X - C ab.1) + 4) * (X - C cd.1) =
      (C cd.2 * (X - C cd.1) + 4) * (X - C ab.1) := by
    apply RatFunc.algebraMap_injective K
    simpa only [map_mul, map_sub, map_add, map_ofNat, RatFunc.algebraMap_C,
      RatFunc.algebraMap_X] using hc
  have hp' := congrArg (Polynomial.eval ab.1) hp
  simp only [eval_mul, eval_add, eval_sub, eval_C, eval_X, eval_ofNat,
    sub_self, mul_zero, zero_add] at hp'
  have ha : ab.1 = cd.1 := by
    have h4 : (4 : K) ≠ 0 := by norm_num
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp').resolve_left h4)
  have hb : ab.2 = cd.2 := by
    unfold planePrivateRoot at he
    rw [ha] at he
    have hh := (div_left_inj' (ratFunc_X_sub_C_ne_zero cd.1)).mp he
    exact RatFunc.C_injective (mul_right_cancel₀ (ratFunc_X_sub_C_ne_zero cd.1)
      (add_right_cancel hh))
  exact Prod.ext ha hb

noncomputable def planeDistancePoly (a b : K) : (RatFunc K)[X] :=
  C (RatFunc.X - RatFunc.C a) * (X - C (RatFunc.C b))

noncomputable def planeRadicandPoly (a b : K) : (RatFunc K)[X] :=
  planeDistancePoly a b * (planeDistancePoly a b - 4)

omit [CharZero K] in
lemma planePrivateRoot_distance (a b : K) :
    (planeDistancePoly a b).eval (planePrivateRoot a b) = 4 := by
  simp only [planeDistancePoly, eval_mul, eval_C, eval_sub, eval_X, planePrivateRoot]
  field_simp [ratFunc_X_sub_C_ne_zero a]
  ring

lemma planePrivateRoot_simple (a b : K) :
    (planeRadicandPoly a b).eval (planePrivateRoot a b) = 0 ∧
    (planeRadicandPoly a b).derivative.eval (planePrivateRoot a b) ≠ 0 := by
  constructor
  · simp [planeRadicandPoly, planePrivateRoot_distance]
  · have h4 : (4 : RatFunc K) ≠ 0 := by norm_num
    have hd : (planeDistancePoly a b).derivative = C (RatFunc.X - RatFunc.C a) := by
      simp [planeDistancePoly]
    simpa [planeRadicandPoly, derivative_mul, derivative_sub,
      planePrivateRoot_distance, hd] using
      mul_ne_zero h4 (ratFunc_X_sub_C_ne_zero a)

lemma planePrivateRoot_other (ab cd : K × K) (h : cd ≠ ab) :
    (planeRadicandPoly cd.1 cd.2).eval (planePrivateRoot ab.1 ab.2) ≠ 0 := by
  simp only [planeRadicandPoly, eval_mul, eval_sub, eval_ofNat, mul_ne_zero_iff]
  constructor
  · simp only [planeDistancePoly, eval_mul, eval_C, eval_sub, eval_X, mul_ne_zero_iff]
    exact ⟨ratFunc_X_sub_C_ne_zero cd.1,
      sub_ne_zero.mpr (planePrivateRoot_ne_constant ab.1 ab.2 cd.2)⟩
  · intro he
    have hd := sub_eq_zero.mp he
    have hroot : planePrivateRoot ab.1 ab.2 = planePrivateRoot cd.1 cd.2 := by
      apply (eq_div_iff (ratFunc_X_sub_C_ne_zero cd.1)).mpr
      simp only [planeDistancePoly, eval_mul, eval_C, eval_sub, eval_X] at hd
      linear_combination hd
    exact h (planePrivateRoot_injective hroot).symm

theorem plane_radicands_squareIndependent (centers : List (K × K))
    (h : centers.Nodup) :
    SquareIndependent (centers.map (fun ab =>
      algebraMap (RatFunc K)[X] (RatFunc (RatFunc K))
        (planeRadicandPoly ab.1 ab.2))) := by
  apply squareIndependent_of_private_simple_roots centers h
  intro ab hab
  exact ⟨planePrivateRoot ab.1 ab.2, (planePrivateRoot_simple ab.1 ab.2).1,
    (planePrivateRoot_simple ab.1 ab.2).2,
    fun cd _ hcd => planePrivateRoot_other ab cd hcd⟩

end Plane

section GenericLine

open Polynomial

variable {B : Type u} {K : Type v} [Field B] [Field K] [Algebra B K]
variable {ι : Type*} {a : ι → K}


variable [CharZero B] [CharZero K]


end GenericLine

section GenericCircle

open Polynomial

variable {B : Type u} {K : Type v} [Field B] [Field K] [Algebra B K]
variable [CharZero B] [CharZero K]
variable {ι : Type*} {a : ι → K}


end GenericCircle
end PlanarUnitDistances.Radicals

namespace PlanarUnitDistances.GenericCurve
open Polynomial
open scoped nonZeroDivisors
variable {K U : Type*} [Field K] [Field U] [Algebra K U]

noncomputable def ratEval (z : U) (hz : Transcendental K z) : RatFunc K →ₐ[K] U :=
  IsFractionRing.liftAlgHom (transcendental_iff_injective.mp hz)

lemma ratEval_polynomial (z : U) (hz : Transcendental K z) (p : K[X]) :
    ratEval z hz (algebraMap K[X] (RatFunc K) p) = aeval z p := by
  change IsFractionRing.lift (transcendental_iff_injective.mp hz)
    (algebraMap K[X] (RatFunc K) p) = _
  exact IsFractionRing.lift_algebraMap _ p

lemma ratEval_comp (z : U) (hz : Transcendental K z) :
    (ratEval z hz).toRingHom.comp (algebraMap K[X] (RatFunc K)) = (aeval z).toRingHom :=
  RingHom.ext (ratEval_polynomial z hz)

@[simp] lemma ratEval_X (z : U) (hz : Transcendental K z) :
    ratEval z hz RatFunc.X=z := by
  simpa only [RatFunc.algebraMap_X,aeval_X] using ratEval_polynomial z hz (X : K[X])

@[simp] lemma ratEval_C (z : U) (hz : Transcendental K z) (a : K) :
    ratEval z hz (RatFunc.C a)=algebraMap K U a := by
  simpa only [RatFunc.algebraMap_C,aeval_C] using ratEval_polynomial z hz (C a)

lemma irreducible_fraction_curve (f : K[X][X]) (hf : Irreducible f)
    (hdeg : f.natDegree ≠ 0) :
    Irreducible (f.map (algebraMap K[X] (RatFunc K))) :=
  (hf.isPrimitive hdeg).irreducible_iff_irreducible_map_fraction_map.mp hf

theorem exists_curve_embedding (f : K[X][X]) (hf : Irreducible f)
    (hdeg : f.natDegree ≠ 0) (z w : U) (hz : Transcendental K z)
    (hroot : f.eval₂ (aeval z).toRingHom w = 0) :
    ∃ φ : AdjoinRoot (f.map (algebraMap K[X] (RatFunc K))) →ₐ[K] U,
      Function.Injective φ ∧
      φ (AdjoinRoot.root _) = w ∧
      (∀ p : K[X], φ (AdjoinRoot.of _ (algebraMap K[X] (RatFunc K) p)) = aeval z p) := by
  let : Fact (Irreducible (f.map (algebraMap K[X] (RatFunc K)))) :=
    ⟨irreducible_fraction_curve f hf hdeg⟩
  have hr : (f.map (algebraMap K[X] (RatFunc K))).eval₂ (ratEval z hz).toRingHom w = 0 := by
    rw [eval₂_map, ratEval_comp]
    exact hroot
  let φ := AdjoinRoot.liftAlgHom (f.map (algebraMap K[X] (RatFunc K))) (ratEval z hz) w hr
  exact ⟨φ, φ.injective, AdjoinRoot.liftAlgHom_root _ _ _ _,
    fun p => (AdjoinRoot.liftAlgHom_of _ _ _ _ _).trans (ratEval_polynomial z hz p)⟩

lemma fiber_separable [CharZero K] (f : K[X][X]) (hf : Irreducible f)
    (hdeg : f.natDegree ≠ 0) (a : U) (ha : Transcendental K a) :
    (f.map (aeval a).toRingHom).Separable := by
  have hs := (irreducible_fraction_curve f hf hdeg).separable.map
    (f := (ratEval a ha).toRingHom)
  rwa [map_map, ratEval_comp] at hs

lemma fiber_degree (f : K[X][X]) (a : U) (ha : Transcendental K a) :
    (f.map (aeval a).toRingHom).natDegree = f.natDegree :=
  natDegree_map_eq_of_injective (transcendental_iff_injective.mp ha) f

lemma fiber_leadingCoeff_ne_zero (f : K[X][X]) (hf : f ≠ 0)
    (a : U) (ha : Transcendental K a) : aeval a f.leadingCoeff ≠ 0 := by
  intro he
  apply leadingCoeff_ne_zero.mpr hf
  exact transcendental_iff_injective.mp ha (he.trans (map_zero _).symm)

lemma separable_exists_root_ne [IsAlgClosed U] (p : U[X])
    (hs : p.Separable) (hd : 2 ≤ p.natDegree) (c : U) :
    ∃ b : U, p.eval b = 0 ∧ b ≠ c := by
  classical
  have hp : p ≠ 0 := by intro hp; simp [hp] at hd
  have hc : p.roots.toFinset.card = p.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hs), IsAlgClosed.card_roots_eq_natDegree]
  by_contra! hn
  have hsub : p.roots.toFinset ⊆ {c} := by
    intro b hb
    simp only [Finset.mem_singleton]
    apply hn b
    exact (mem_roots hp).mp (Multiset.mem_toFinset.mp hb)
  have hcard := Finset.card_le_card hsub
  rw [hc, Finset.card_singleton] at hcard
  omega

theorem exists_distinct_smooth_sheet [CharZero K] [IsAlgClosed U]
    (f : K[X][X]) (hf : Irreducible f) (hdeg : f.natDegree ≠ 0)
    (a c : U) (ha : Transcendental K a)
    (halt : f.eval₂ (aeval a).toRingHom c ≠ 0 ∨ 2 ≤ f.natDegree) :
    ∃ b : U, f.eval₂ (aeval a).toRingHom b = 0 ∧
      f.derivative.eval₂ (aeval a).toRingHom b ≠ 0 ∧ b ≠ c := by
  let p := f.map (aeval a).toRingHom
  have hs : p.Separable := fiber_separable f hf hdeg a ha
  have hd : p.natDegree = f.natDegree := fiber_degree f a ha
  obtain ⟨b, hb, hbc⟩ : ∃ b : U, p.eval b = 0 ∧ b ≠ c := by
    rcases halt with hnc | htwo
    · obtain ⟨b, hb⟩ := IsAlgClosed.exists_root p (fun h => (hd.trans_ne hdeg) (natDegree_eq_zero_iff_degree_le_zero.mpr h.le))
      change p.eval b = 0 at hb
      refine ⟨b, hb, ?_⟩
      intro he
      subst b
      exact hnc (by simpa only [p, eval_map] using hb)
    · exact separable_exists_root_ne p hs (hd ▸ htwo) c
  refine ⟨b, ?_, ?_, hbc⟩
  · simpa only [p, eval_map] using hb
  · have hh := hs.eval₂_derivative_ne_zero (RingHom.id U) (x := b) (by simpa using hb)
    simpa only [eval₂_id, p, derivative_map, eval_map] using hh

end PlanarUnitDistances.GenericCurve

namespace PlanarUnitDistances.GenericPlane
open Polynomial
variable {K U : Type*} [Field K] [Field U] [Algebra K U]

theorem exists_plane_embedding (x : Fin 2 → U) (hx : AlgebraicIndependent K x) :
    ∃ f : RatFunc (RatFunc K) →+* U,
      f (RatFunc.X : RatFunc (RatFunc K)) = x 1 ∧
      f (RatFunc.C (RatFunc.X : RatFunc K)) = x 0 ∧
      ∀ a : K, f (RatFunc.C (RatFunc.C a)) = algebraMap K U a := by
  let E := IntermediateField.adjoin K ({x 0} : Set U)
  let z : E := ⟨x 0, IntermediateField.subset_adjoin K _ (Set.mem_singleton _)⟩
  have hz : Transcendental K z := by
    intro h
    exact hx.transcendental 0 (h.algHom E.val)
  have hw : Transcendental E (x 1) := by
    apply IntermediateField.transcendental_adjoin_iff.mpr
    have hh := hx.transcendental_adjoin (s := {(0 : Fin 2)}) (i := 1) (by decide)
    rw [Set.image_singleton] at hh
    exact hh
  let g : RatFunc K →ₐ[K] E := GenericCurve.ratEval z hz
  let φ : (RatFunc K)[X] →+* U := (aeval (x 1) : E[X] →ₐ[E] U).toRingHom.comp
    (Polynomial.mapRingHom g.toRingHom)
  have hφ : Function.Injective φ :=
    (transcendental_iff_injective.mp hw).comp (Polynomial.map_injective g.toRingHom g.injective)
  let f : RatFunc (RatFunc K) →+* U := IsFractionRing.lift hφ
  have hf (p : (RatFunc K)[X]) : f (algebraMap (RatFunc K)[X] _ p)=φ p :=
    IsFractionRing.lift_algebraMap hφ p
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [← RatFunc.algebraMap_X, hf]
    simp [φ]
  · rw [← RatFunc.algebraMap_C, hf]
    change aeval (x 1) ((C RatFunc.X).map g.toRingHom) = x 0
    rw [Polynomial.map_C, aeval_C]
    change (g RatFunc.X : U) = x 0
    simp [g,z]
  · intro a
    rw [← RatFunc.algebraMap_C, hf]
    change aeval (x 1) ((C (RatFunc.C a)).map g.toRingHom) = algebraMap K U a
    rw [Polynomial.map_C, aeval_C]
    change (g (RatFunc.C a) : U) = algebraMap K U a
    simp [g]
end PlanarUnitDistances.GenericPlane

namespace PlanarUnitDistances.Radicals
universe u
variable {k K L : Type u} [Field k] [Field K] [CharZero K] [Field L]
  [Algebra k L] [Algebra K L]

end PlanarUnitDistances.Radicals

namespace PlanarUnitDistances.Radicals
open Polynomial
universe u
variable {k B K L : Type u} [Field k] [Field B] [CharZero B] [Field K] [CharZero K]
  [Field L] [Algebra k L] [Algebra B K] [Algebra K L] [IsAlgClosed K]

end PlanarUnitDistances.Radicals

namespace PlanarUnitDistances.Radicals
open Polynomial
universe u
variable {K : Type u} [Field K]


variable {k B L : Type u} [Field k] [Field B] [CharZero B] [CharZero K]
  [Field L] [Algebra k L] [Algebra B K] [Algebra K L] [IsAlgClosed K]

end PlanarUnitDistances.Radicals

end OAI
