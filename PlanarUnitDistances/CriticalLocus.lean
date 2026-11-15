/- The extension of derivations and the transcendence-basis argument in the first two
sections are adapted from OpenAI math, UnitDistances/Derivations.lean, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0). -/
import Mathlib

/-! Constancy of the output on components of the polynomial multiplier locus. -/

noncomputable section

namespace PlanarUnitDistances.CriticalLocus

open TensorProduct

section Etale
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [Algebra.FormallyEtale S T]

noncomputable def extendDerivation (d : Derivation R S T) : Derivation R T T :=
  ((d.liftKaehlerDifferential.liftBaseChange T).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap).compDer
      (KaehlerDifferential.D R T)

@[simp] theorem extendDerivation_algebraMap (d : Derivation R S T) (s : S) :
    extendDerivation d (algebraMap S T s) = d s := by
  simp [extendDerivation,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]

end Etale

section Fields
variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero k]

theorem exists_derivation_basis_one {ι : Type*} (b : ι → F)
    (hb : IsTranscendenceBasis k b) (i : ι) :
    ∃ d : Derivation k F F, d (b i) = 1 := by
  classical
  let P := MvPolynomial ι k
  let Q := FractionRing P
  let E := IntermediateField.adjoin k (Set.range b)
  let e : Q ≃ₐ[k] E := hb.1.aevalEquivField
  let f : Q →ₐ[k] F := E.val.comp e.toAlgHom
  let : Algebra Q F := f.toRingHom.toAlgebra
  have : IsScalarTower k Q F := IsScalarTower.of_algebraMap_eq fun x => by
    exact (f.commutes x).symm
  have : Algebra.IsAlgebraic E F := hb.isAlgebraic_field
  have : Algebra.IsAlgebraic Q F :=
    Algebra.IsAlgebraic.of_ringHom_of_comp_eq e.toRingHom (RingHom.id F)
      e.surjective Function.injective_id rfl
  have : CharZero Q := inferInstance
  have : Algebra.FormallyEtale Q F := Algebra.FormallyEtale.of_isSeparable Q F
  let dP : Derivation k P Q := MvPolynomial.mkDerivation k (fun j => if j = i then 1 else 0)
  let dQ : Derivation k Q Q := extendDerivation dP
  let dQF : Derivation k Q F := (Algebra.linearMap Q F).compDer dQ
  refine ⟨extendDerivation dQF, ?_⟩
  have hbi : algebraMap Q F (algebraMap P Q (MvPolynomial.X i)) = b i := by
    change (e (algebraMap P Q (MvPolynomial.X i)) : F) = b i
    rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
    simp
  rw [← hbi, extendDerivation_algebraMap]
  change algebraMap Q F (extendDerivation dP
    (algebraMap P Q (MvPolynomial.X i))) = 1
  rw [extendDerivation_algebraMap]
  have heval : dP (MvPolynomial.X i) = 1 := by
    change MvPolynomial.mkDerivation k (fun j => if j = i then (1 : Q) else 0)
      (MvPolynomial.X i) = 1
    rw [MvPolynomial.mkDerivation_X]
    simp
  rw [heval, map_one]

theorem exists_derivation_one {x : F} (hx : Transcendental k x) :
    ∃ d : Derivation k F F, d x = 1 := by
  have hs : AlgebraicIndepOn k id ({x} : Set F) := by
    apply (algebraicIndependent_singleton_iff ⟨x, by simp⟩).mpr
    exact hx
  obtain ⟨b, hxb, hb⟩ := exists_isTranscendenceBasis_superset hs
  exact exists_derivation_basis_one Subtype.val hb ⟨x, hxb (by simp)⟩

end Fields

open MvPolynomial
open scoped BigOperators

section CriticalValue

variable {k L X R : Type*} [Field k] [Field L] [Algebra k L] [Fintype X]

/-- Chain rule at an extension-field valued point, for an arbitrary base derivation. -/
theorem derivation_aeval (d : Derivation k L L) (x : X → L) (f : MvPolynomial X k) :
    d (aeval x f) = ∑ i, aeval x (pderiv i f) * d (x i) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [add_mul, Finset.sum_add_distrib, hf, hg]
  | mul_X f j hf =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, aeval_X, map_add, pderiv_X,
      Pi.single_apply, hf, add_mul, Finset.sum_add_distrib]
    simp only [apply_ite, map_one, map_zero, mul_one, mul_zero, ite_mul, zero_mul]
    rw [Finset.mul_sum]
    ring_nf
    simp [add_comm]

/-- The gradient identity on the zero set forces algebraicity even if the coefficient
field is not algebraically closed. -/
theorem critical_value_isAlgebraic [CharZero k] [Fintype R]
    (x : X → L) (t : R → L) (f : MvPolynomial X k) (g : R → MvPolynomial X k)
    (hg : ∀ r, aeval x (g r) = 0)
    (hgrad : ∀ i, aeval x (pderiv i f) = ∑ r, t r * aeval x (pderiv i (g r))) :
    IsAlgebraic k (aeval x f) := by
  by_contra ht
  obtain ⟨d, hd⟩ := exists_derivation_one ht
  have hzero : d (aeval x f) = 0 := by
    calc
      _ = ∑ i, (∑ r, t r * aeval x (pderiv i (g r))) * d (x i) := by
        simp_rw [derivation_aeval d x f, hgrad]
      _ = ∑ r, t r * d (aeval x (g r)) := by
        simp_rw [Finset.sum_mul, mul_assoc, derivation_aeval d x (g _), Finset.mul_sum]
        exact Finset.sum_comm
      _ = 0 := by simp [hg]
  exact one_ne_zero (hd.symm.trans hzero)

end CriticalValue

section CriticalComponent

variable {k A X R : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing A] [IsDomain A] [Algebra k A] [Fintype X] [Fintype R]

/-- Passing to the function field and back proves equality in the coordinate
ring itself, including at singular points of the component. -/
theorem critical_value_in_coordinate_ring (x : X → A) (t : R → A) (f : MvPolynomial X k)
    (g : R → MvPolynomial X k) (hg : ∀ r, aeval x (g r) = 0)
    (hgrad : ∀ i, aeval x (pderiv i f) = ∑ r, t r * aeval x (pderiv i (g r))) :
    ∃ c : k, aeval x f = algebraMap k A c := by
  let L := FractionRing A
  let inc : A →ₐ[k] L := IsScalarTower.toAlgHom k A L
  have hz (r : R) : aeval (fun i ↦ inc (x i)) (g r) = 0 := by
    rw [← comp_aeval_apply, hg, map_zero]
  have hj (i : X) : aeval (fun j ↦ inc (x j)) (pderiv i f) =
      ∑ r, inc (t r) * aeval (fun j ↦ inc (x j)) (pderiv i (g r)) := by
    simpa only [comp_aeval_apply, map_sum, map_mul] using congrArg inc (hgrad i)
  have halg := critical_value_isAlgebraic _ _ _ _ hz hj
  have hmem := (mem_algebraicClosure_iff.mpr halg)
  rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure k L)] at hmem
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hmem
  refine ⟨c, IsFractionRing.injective A L ?_⟩
  change inc (aeval x f) = inc (algebraMap k A c)
  rw [comp_aeval_apply, inc.commutes]
  exact hc.symm

end CriticalComponent

section Incidence

variable {k X A R : Type*} [Field k] [Fintype R]

/-- Separate coordinates for the original variables, selected row multipliers, and output. -/
abbrev Variables (X R : Type*) := X ⊕ (R ⊕ Unit)

def liftedPoint {L : Type*} (x : X → L) (t : R → L) (c : L) : Variables X R → L :=
  Sum.elim x (Sum.elim t (fun _ ↦ c))

def outputVariable : MvPolynomial (Variables X R) k := MvPolynomial.X (.inr (.inr ()))

/-- The original equations, the gradient relations, and the single output equation.
All original equations are retained, including unselected rows. -/
def incidenceEquation (f : MvPolynomial X k) (g : A → MvPolynomial X k) (pick : R → A) :
    A ⊕ (X ⊕ Unit) → MvPolynomial (Variables X R) k
  | .inl a => rename Sum.inl (g a)
  | .inr (.inl i) => rename Sum.inl (pderiv i f) -
      ∑ r, MvPolynomial.X (.inr (.inl r)) * rename Sum.inl (pderiv i (g (pick r)))
  | .inr (.inr ()) => outputVariable - rename Sum.inl f

def incidenceIdeal (f : MvPolynomial X k) (g : A → MvPolynomial X k) (pick : R → A) :
    Ideal (MvPolynomial (Variables X R) k) :=
  Ideal.span (Set.range (incidenceEquation f g pick))

/-- Differentiating a polynomial of degree at most `d + 1` removes at least
one degree from every surviving monomial. This includes the zero derivative. -/
theorem totalDegree_pderiv_le {p : MvPolynomial X k} {d : ℕ} (i : X)
    (hp : p.totalDegree ≤ d + 1) : (pderiv i p).totalDegree ≤ d := by
  classical
  apply Finset.sup_le
  intro m hm
  have hn := mem_support_iff.mp hm
  rw [coeff_pderiv] at hn
  have hs : m + Finsupp.single i 1 ∈ p.support :=
    mem_support_iff.mpr (left_ne_zero_of_mul hn)
  have hd := (le_totalDegree hs).trans hp
  simpa [Finsupp.sum_add_index'] using hd

/-- All the incidence equations are quadrics when the input polynomials are
quadrics. This accounts for the new multiplier in a gradient equation. -/
theorem incidenceEquation_quadratic (f : MvPolynomial X k) (g : A → MvPolynomial X k)
    (pick : R → A) (hf : f.totalDegree ≤ 2) (hg : ∀ a, (g a).totalDegree ≤ 2)
    (j : A ⊕ (X ⊕ Unit)) : (incidenceEquation f g pick j).totalDegree ≤ 2 := by
  rcases j with a | (i | ⟨⟩)
  · exact (totalDegree_rename_le _ _).trans (hg a)
  · apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (totalDegree_rename_le _ _).trans ((totalDegree_pderiv_le i hf).trans (by decide))
    · apply totalDegree_finsetSum_le
      intro r _
      apply (totalDegree_mul _ _).trans
      rw [totalDegree_X]
      have ht := (totalDegree_rename_le (Sum.inl : X → Variables X R) _).trans
        (totalDegree_pderiv_le (d := 1) i (hg (pick r)))
      omega
  · apply (totalDegree_sub _ _).trans
    exact max_le (by simp [outputVariable]) ((totalDegree_rename_le _ _).trans hf)

theorem liftedPoint_zero {L : Type*} [Field L] [Algebra k L] (x : X → L) (t : R → L)
    (f : MvPolynomial X k) (g : A → MvPolynomial X k) (pick : R → A)
    (hz : ∀ a, aeval x (g a) = 0)
    (hj : ∀ i, aeval x (pderiv i f) = ∑ r, t r * aeval x (pderiv i (g (pick r)))) :
    incidenceIdeal f g pick ≤ RingHom.ker (aeval (liftedPoint x t (aeval x f))) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨a | (i | ⟨⟩), rfl⟩
  · simpa [incidenceEquation, aeval_rename, liftedPoint, Function.comp_def] using hz a
  · simpa [incidenceEquation, aeval_rename, liftedPoint, Function.comp_def, sub_eq_zero] using hj i
  · simp [incidenceEquation, outputVariable, aeval_rename, liftedPoint, Function.comp_def]

/-- On every prime closed subset of the multiplier locus the output equals a base
scalar modulo the prime ideal, independently of regularity or Jacobian rank. -/
theorem output_constant_mod_prime [CharZero k] [IsAlgClosed k] [Fintype X]
    (f : MvPolynomial X k) (g : A → MvPolynomial X k) (pick : R → A)
    (P : Ideal (MvPolynomial (Variables X R) k)) [P.IsPrime]
    (hP : incidenceIdeal f g pick ≤ P) :
    ∃ c : k, outputVariable - C c ∈ P := by
  let q := Ideal.Quotient.mkₐ k P
  let x (i : X) := q (MvPolynomial.X (Sum.inl i))
  let t (r : R) := q (MvPolynomial.X (Sum.inr (Sum.inl r)))
  have hrename (p : MvPolynomial X k) : q (rename Sum.inl p) = aeval x p := by
    have he : q.comp (rename (Sum.inl : X → Variables X R)) = aeval x := by
      ext i
      simp [x]
    exact AlgHom.congr_fun he p
  have heq (j) : q (incidenceEquation f g pick j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hP (Ideal.subset_span ⟨j, rfl⟩))
  have hz (r : R) : aeval x (g (pick r)) = 0 := by
    rw [← hrename]
    exact heq (.inl (pick r))
  have hj (i : X) : aeval x (pderiv i f) = ∑ r, t r * aeval x (pderiv i (g (pick r))) := by
    simpa only [incidenceEquation, map_sub, sub_eq_zero, map_sum, map_mul, hrename, t] using
      heq (.inr (.inl i))
  obtain ⟨c, hc⟩ := critical_value_in_coordinate_ring x t f (fun r ↦ g (pick r)) hz hj
  refine ⟨c, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  change q (outputVariable - C c) = 0
  have hout : q outputVariable = aeval x f := by
    simpa only [incidenceEquation, map_sub, sub_eq_zero, hrename] using heq (.inr (.inr ()))
  rw [map_sub, sub_eq_zero, hout, hc]
  exact (q.commutes c).symm

/-- A stationary extension-field point lifts to an actual minimal prime component,
whose scalar output specializes to the output of the given point. -/
theorem component_through_stationary_point [CharZero k] [IsAlgClosed k] [Fintype X]
    {L : Type*} [Field L] [Algebra k L] (x : X → L) (t : R → L)
    (f : MvPolynomial X k) (g : A → MvPolynomial X k) (pick : R → A)
    (hz : ∀ a, aeval x (g a) = 0)
    (hj : ∀ i, aeval x (pderiv i f) = ∑ r, t r * aeval x (pderiv i (g (pick r)))) :
    ∃ P ∈ (incidenceIdeal f g pick).minimalPrimes,
      P ≤ RingHom.ker (aeval (liftedPoint x t (aeval x f))) ∧
        ∃ c : k, outputVariable - C c ∈ P ∧ aeval x f = algebraMap k L c := by
  let φ := aeval (R := k) (liftedPoint x t (aeval x f))
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨P, hp, hpk⟩ := Ideal.exists_minimalPrimes_le (J := RingHom.ker φ)
    (liftedPoint_zero x t f g pick hz hj)
  haveI : P.IsPrime := hp.isPrime
  obtain ⟨c, hc⟩ := output_constant_mod_prime f g pick P hp.le
  refine ⟨P, hp, hpk, c, hc, ?_⟩
  have := RingHom.mem_ker.mp (hpk hc)
  simpa [φ, outputVariable, liftedPoint, sub_eq_zero] using this

end Incidence

section Stationarity

variable {k L X A : Type*} [Field k] [Field L] [Algebra k L] [Fintype X]

/-- The Jacobian row covector on velocities of the original polynomial coordinates. -/
def jacobianRow (x : X → L) (f : MvPolynomial X k) : (X → L) →ₗ[L] L :=
  ∑ i, aeval x (pderiv i f) • LinearMap.proj i

theorem jacobianRow_single [DecidableEq X] (x : X → L) (f : MvPolynomial X k) (i : X) :
    jacobianRow x f (Pi.single i 1) = aeval x (pderiv i f) := by
  simp [jacobianRow, LinearMap.sum_apply, Pi.single_apply, mul_ite]

/-- Without any multipliers given in advance, stationarity on the full
Jacobian kernel selects independent rows, lifts to the incidence locus with
exactly the rank many multipliers, and finds a component through the point
whose regular output function is a scalar. -/
theorem stationary_coordinate_component [CharZero k] [IsAlgClosed k] [Finite A]
    (x : X → L) (f : MvPolynomial X k) (g : A → MvPolynomial X k)
    (hz : ∀ a, aeval x (g a) = 0)
    (hstat : ∀ v : X → L, (∀ a, jacobianRow x (g a) v = 0) → jacobianRow x f v = 0) :
    ∃ (r : ℕ) (pick : Fin r → A) (t : Fin r → L),
      r = Module.finrank L (Submodule.span L (Set.range (fun a ↦ jacobianRow x (g a)))) ∧
      LinearIndependent L (fun j ↦ jacobianRow x (g (pick j))) ∧
      ∃ P ∈ (incidenceIdeal f g pick).minimalPrimes,
        P ≤ RingHom.ker (aeval (liftedPoint x t (aeval x f))) ∧
          ∃ c : k, outputVariable - C c ∈ P ∧ aeval x f = algebraMap k L c := by
  classical
  let row (a : A) := jacobianRow x (g a)
  have hf : jacobianRow x f ∈ Submodule.span L (Set.range row) :=
    mem_span_of_iInf_ker_le_ker (show (⨅ a, (row a).ker) ≤ (jacobianRow x f).ker from
      fun v hv ↦ hstat v (fun a ↦ (Submodule.mem_iInf _).mp hv a))
  obtain ⟨b, hb, hspan, hlin⟩ := Submodule.exists_fun_fin_finrank_span_eq L (Set.range row)
  choose pick hpick using hb
  have hrow : (fun j ↦ row (pick j)) = b := funext hpick
  rw [← hspan] at hf
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hf
  refine ⟨_, pick, t, rfl, ?_, ?_⟩
  · change LinearIndependent L (fun j ↦ row (pick j))
    rwa [hrow]
  apply component_through_stationary_point x t f g pick hz
  intro i
  rw [← hrow] at ht
  have h := LinearMap.congr_fun ht (Pi.single i 1)
  simpa only [row, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    jacobianRow_single] using h.symm

end Stationarity

end PlanarUnitDistances.CriticalLocus
