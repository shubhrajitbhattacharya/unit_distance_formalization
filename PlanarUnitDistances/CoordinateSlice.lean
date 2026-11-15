import Mathlib

namespace PlanarUnitDistances.CoordinateSlice

open MvPolynomial Set

noncomputable section

variable {k V : Type*} [Field k]
abbrev Poly (k V : Type*) [Field k] := MvPolynomial V k

def residue (P : Ideal (Poly k V)) (v : V) : (Poly k V ⧸ P) :=
  Ideal.Quotient.mk P (X v)

theorem residue_aeval (P : Ideal (Poly k V)) :
    aeval (residue P) = Ideal.Quotient.mkₐ k P := by
  ext v
  simp [residue]

theorem coordinate_basis (P : Ideal (Poly k V)) [P.IsPrime] :
    ∃ S : Set V, IsTranscendenceBasis k (fun i : S => residue P i.1) := by
  classical
  let z := residue P
  have gen : Algebra.adjoin k (range z) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, show aeval z=Ideal.Quotient.mkₐ k P from residue_aeval P]
    apply top_unique
    intro y _
    obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨f,rfl⟩
  haveI : Algebra.IsAlgebraic (Algebra.adjoin k (range z)) (Poly k V ⧸ P) := by
    rw [gen]
    exact ⟨fun x => isAlgebraic_algebraMap (A := Poly k V ⧸ P) (⟨x,by simp⟩ : (⊤ : Subalgebra k _))⟩
  letI : FaithfulSMul k (Poly k V ⧸ P) := (faithfulSMul_iff_algebraMap_injective k _).mpr (algebraMap k (Poly k V ⧸ P)).injective
  obtain ⟨B,hB,basis⟩ := exists_isTranscendenceBasis_subset (R:=k) (range z)
  choose pick hp using fun b : B => hB b.prop
  have hp' : Function.Injective pick := fun u v e => Subtype.ext ((hp u).symm.trans ((congrArg z e).trans (hp v)))
  let e := Equiv.ofInjective pick hp'
  refine ⟨range pick,(isTranscendenceBasis_equiv' e (f:=fun i : range pick => z i.1)
    (g:=fun b : B => (b : Poly k V ⧸ P)) ?_).mp basis⟩
  exact funext hp

/-- All nonzero polynomials in precisely the selected coordinates. -/
def denominators (k : Type*) [Field k] {V : Type*} (S : Set V) : Submonoid (Poly k V) :=
  (nonZeroDivisors (Poly k S)).map (rename (R:=k) ((↑) : S → V)).toRingHom.toMonoidHom

theorem residue_rename (P : Ideal (Poly k V)) (S : Set V) (f : Poly k S) :
    Ideal.Quotient.mk P (rename ((↑) : S → V) f) = aeval (fun i : S => residue P i.1) f := by
  change Ideal.Quotient.mkₐ k P _ = _
  rw [← residue_aeval]
  exact aeval_rename _ _ _

theorem basis_disjoint {P : Ideal (Poly k V)} {S : Set V}
    (basis : IsTranscendenceBasis k (fun i : S => residue P i.1)) :
    Disjoint (denominators k S : Set (Poly k V)) (P : Set (Poly k V)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨p,hp,rfl⟩ hP
  have hz := (Ideal.Quotient.eq_zero_iff_mem (I:=P)).mpr hP
  change Ideal.Quotient.mk P (rename ((↑) : S → V) p) = 0 at hz
  rw [residue_rename] at hz
  exact nonZeroDivisors.ne_zero hp (algebraicIndependent_iff.mp basis.1 p hz)

/-- Every ideal strictly above the chosen prime meets the same coordinate denominators. -/
theorem denominator_in_larger_ideal {P Q : Ideal (Poly k V)} [P.IsPrime] {S : Set V}
    (basis : IsTranscendenceBasis k (fun i : S => residue P i.1)) (hPQ : P < Q) :
    ∃ x ∈ denominators k S, x ∈ Q := by
  let A := Algebra.adjoin k (range (fun i : S => residue P i.1))
  let J := Q.map (Ideal.Quotient.mk P)
  obtain ⟨y,hyQ,hyP⟩ := IsConcreteLE.exists_of_lt hPQ
  have hy : Ideal.Quotient.mk P y ≠ 0 := fun h => hyP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hne : J.under A ≠ ⊥ :=
    J.under_ne_bot_of_algebraic_mem hy (Ideal.mem_map_of_mem _ hyQ)
      (basis.isAlgebraic.1 (Ideal.Quotient.mk P y))
  obtain ⟨a,ha,ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have aRange := a.prop
  change (a : Poly k V ⧸ P) ∈ Algebra.adjoin k _ at aRange
  rw [Algebra.adjoin_range_eq_range_aeval] at aRange
  obtain ⟨f,hf⟩ := aRange
  change aeval (fun i : S => residue P i.1) f = (a : Poly k V ⧸ P) at hf
  have fne : f≠0 := by
    rintro rfl
    apply ha0
    exact Subtype.ext (by simpa using hf.symm)
  refine ⟨rename ((↑) : S → V) f,⟨f,mem_nonZeroDivisors_of_ne_zero fne,rfl⟩,?_⟩
  rw [←Ideal.comap_map_mk hPQ.le]
  change Ideal.Quotient.mk P _ ∈ J
  rw [residue_rename,hf]
  exact ha

theorem slice_at_basis {I P : Ideal (Poly k V)} (hP : P ∈ I.minimalPrimes)
    {S : Set V} (basis : IsTranscendenceBasis k (fun i : S => residue P i.1))
    (T : Type*) [CommRing T] [Algebra (Poly k V) T] [IsLocalization (denominators k S) T] :
    let f := algebraMap (Poly k V) T
    (P.map f).IsMaximal ∧ P.map f ∈ (I.map f).minimalPrimes ∧ (P.map f).comap f = P := by
  classical
  let M := denominators k S
  let f := algebraMap (Poly k V) T
  letI := hP.isPrime
  have hd := basis_disjoint basis
  have under : (P.map f).under (Poly k V) = P := IsLocalization.under_map_of_isPrime_disjoint M T hP.isPrime hd
  have prime := IsLocalization.isPrime_of_isPrime_disjoint M T P hP.isPrime hd
  refine ⟨Ideal.isMaximal_def.mpr ⟨prime.ne_top,?_⟩,?_,under⟩
  · intro L hL
    by_contra hlt
    have str : P < L.under (Poly k V) := by
      rw [←under]
      exact (IsLocalization.orderEmbedding M T).strictMono hL
    obtain ⟨x,hx,hxL⟩ := denominator_in_larger_ideal basis str
    exact Set.disjoint_left.mp ((IsLocalization.disjoint_under_iff M T L).mpr hlt) hx hxL
  · rw [IsLocalization.minimalPrimes_map M T]
    change (P.map f).under (Poly k V) ∈ I.minimalPrimes
    rwa [under]


end
end PlanarUnitDistances.CoordinateSlice
