import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! An irreducible polynomial over an algebraically closed field stays
irreducible after enlarging the constant field. Specializing the coefficient
algebra of a hypothetical factorization preserves both factor supports. -/

namespace PlanarUnitDistances.GeometricIrreducibility
open MvPolynomial
noncomputable section

private theorem specialization (k A : Type*) [Field k] [IsAlgClosed k] [CommRing A] [Nontrivial A]
    [Algebra k A] [Algebra.FiniteType k A] : Nonempty (A →ₐ[k] k) := by
  obtain ⟨m,hm⟩ := Ideal.exists_maximal A
  letI := hm
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  letI := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  exact ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m)⟩

private theorem unit_of_support {σ k l : Type*} [Field k] [Field l]
    {p : MvPolynomial σ k} {q : MvPolynomial σ l} (h : p.support=q.support) (hu : IsUnit p) :
    IsUnit q := by
  obtain ⟨hc,hd⟩ := isUnit_iff_totalDegree_of_isReduced.mp hu
  apply isUnit_iff_totalDegree_of_isReduced.mpr
  constructor
  · apply isUnit_iff_ne_zero.mpr
    rw [← mem_support_iff,← h,mem_support_iff]
    exact hc.ne_zero
  · simpa only [totalDegree,← h] using hd

/-- Absolute irreducibility of a multivariate polynomial over an
algebraically closed ground field. The extending field may have any
transcendence degree, and the variable set need not be finite. -/
theorem irreducible_map {k L σ : Type*} [Field k] [IsAlgClosed k] [Field L] [Algebra k L]
    (f : MvPolynomial σ k) (irr : Irreducible f) : Irreducible (map (algebraMap k L) f) := by
  classical
  refine ⟨fun h ↦ irr.not_isUnit (unit_of_support
    (support_map_of_injective f (algebraMap k L).injective) h),?_⟩
  intro p q fac
  let s := p.coeffs ∪ q.coeffs
  let t := s ∪ s.image (fun c : L ↦ c⁻¹)
  let R := Algebra.adjoin k (t : Set L)
  let j := R.val.toRingHom
  letI : Algebra.FiniteType k R := Algebra.FiniteType.adjoin_of_finite t.finite_toSet
  obtain ⟨ψ⟩ := specialization k R
  have ins {c : L} (hc : c ∈ s) : c ∈ R := Algebra.subset_adjoin (Finset.mem_union_left _ hc)
  have invs {c : L} (hc : c ∈ s) : c⁻¹ ∈ R :=
    Algebra.subset_adjoin (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc))
  have lift (g : MvPolynomial σ L) (subset : g.coeffs ⊆ s) :
      ∃ g' : MvPolynomial σ R, map j g'=g ∧ (map ψ.toRingHom g').support=g.support := by
    have range : g ∈ Set.range (map (σ := σ) j) := mem_range_map_iff_coeffs_subset.mpr
      (fun c hc ↦ ⟨⟨c,ins (subset hc)⟩,rfl⟩)
    obtain ⟨g',hg'⟩ := range
    refine ⟨g',hg',?_⟩
    ext d
    rw [mem_support_iff,mem_support_iff,coeff_map]
    have dc : ((g'.coeff d : R):L)=g.coeff d := by
      change j (g'.coeff d)=g.coeff d
      have e := congrArg (fun z : MvPolynomial σ L ↦ z.coeff d) hg'
      simpa only [coeff_map] using e
    constructor
    · intro h hzero
      have ze : g'.coeff d=0 := Subtype.ext (dc.trans hzero)
      exact h (by simp [ze])
    · intro h
      have invmem := invs (subset (coeff_mem_coeffs d h))
      have un : IsUnit (g'.coeff d) := isUnit_iff_exists_inv.mpr
        ⟨⟨(g.coeff d)⁻¹,invmem⟩,Subtype.ext (by change ((g'.coeff d:R):L)*(g.coeff d)⁻¹=1; rw [dc,mul_inv_cancel₀ h])⟩
      exact (un.map ψ.toRingHom).ne_zero
  obtain ⟨p',hp,hps⟩ := lift p Finset.subset_union_left
  obtain ⟨q',hq,hqs⟩ := lift q Finset.subset_union_right
  have eqR : map (algebraMap k R) f=p'*q' := by
    apply map_injective j Subtype.val_injective
    rw [map_map,map_mul,hp,hq]
    exact fac
  have eqk : f=map ψ.toRingHom p'*map ψ.toRingHom q' := by
    have e := congrArg (map (σ := σ) ψ.toRingHom) eqR
    have r : ψ.toRingHom.comp (algebraMap k R)=RingHom.id k := by
      ext c
      exact ψ.commutes c
    simpa only [map_map,r,map_id,map_mul] using e
  exact (irr.isUnit_or_isUnit eqk).imp (unit_of_support hps) (unit_of_support hqs)

end
end PlanarUnitDistances.GeometricIrreducibility
