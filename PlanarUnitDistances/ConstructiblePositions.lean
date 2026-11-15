import PlanarUnitDistances.GridElimination
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace PlanarUnitDistances.Competition.GridElimination
open MvPolynomial Topology
open scoped Classical
noncomputable section
variable {k I J N : Type*} [Field k] [IsAlgClosed k] [Finite I] [Finite J] [Finite N]

omit [IsAlgClosed k] [Finite I] in
private theorem point_mem (x : I → k) (p : MvPolynomial I k) :
    p ∈ (pointToPoint (k:=k) x).asIdeal ↔ eval x p = 0 :=
  mem_vanishingIdeal_singleton_iff x p

omit [IsAlgClosed k] [Finite I] [Finite J] in
private theorem project_point (c : I → J) (y : J → k) :
    PrimeSpectrum.comap (rename c (R:=k)).toRingHom (pointToPoint (k:=k) y) =
      pointToPoint (k:=k) (y ∘ c) := by
  apply PrimeSpectrum.ext
  ext p
  change rename c p ∈ (pointToPoint (k:=k) y).asIdeal ↔ p ∈ (pointToPoint (k:=k) (y ∘ c)).asIdeal
  rw [point_mem,point_mem,eval_rename]

omit [Finite I] [Finite N] in
/-- The projection of a closed affine set on actual field-valued points is
the pullback of its prime-spectrum image under the closed-point map.
The inclusion from right to left lifts the given point without replacing it
by a specialization of the target. -/
theorem lift_projected_closed_point (c : I → J) (q : N → MvPolynomial J k) (x : I → k) :
    (∃ y : J → k, (∀ i, eval y (q i)=0) ∧ y ∘ c = x) ↔
    pointToPoint (k:=k) x ∈ PrimeSpectrum.comap (rename c (R:=k)).toRingHom ''
      PrimeSpectrum.zeroLocus (Set.range q) := by
  constructor
  · rintro ⟨y,h,rfl⟩
    refine ⟨pointToPoint (k:=k) y,?_,project_point c y⟩
    rintro _ ⟨i,rfl⟩
    exact (point_mem _ _).mpr (h i)
  · rintro ⟨p,hp,hpx⟩
    obtain ⟨m,hm,hle⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
    obtain ⟨y,hmx⟩ := eq_vanishingIdeal_singleton_of_isMaximal k hm
    have vanish (a : MvPolynomial J k) (ha : a ∈ p.asIdeal) : eval y a=0 :=
      (mem_vanishingIdeal_singleton_iff y a).mp (hmx ▸ hle ha)
    refine ⟨y, fun i => vanish _ (hp (Set.mem_range_self i)),?_⟩
    funext i
    let a : MvPolynomial I k := X i-C (x i)
    have ax : a ∈ (pointToPoint (k:=k) x).asIdeal := (point_mem _ _).mpr (by simp [a])
    rw [← hpx] at ax
    have h := vanish _ (show rename c a ∈ p.asIdeal from ax)
    simpa [a,eval_rename,sub_eq_zero] using h

omit [IsAlgClosed k] in
private theorem rename_fp (c : I → J) : (rename c (R:=k)).toRingHom.FinitePresentation := by
  apply RingHom.FinitePresentation.of_finiteType.mp
  apply RingHom.FiniteType.of_comp_finiteType (f:=C)
  have h : (rename c (R:=k)).toRingHom.comp C = C := by ext a; simp
  rw [h]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- A finite union of charts, each defined on the concrete affine space by
a finite family of equations and one polynomial inequation. -/
theorem projected_equation_charts (c : I → J) (q : N → MvPolynomial J k) :
    ∃ T : Finset (Finset (MvPolynomial I k) × MvPolynomial I k), ∀ x : I → k,
      (∃ y : J → k, (∀ i, eval y (q i)=0) ∧ y ∘ c = x) ↔
        ∃ t ∈ T, (∀ p ∈ t.1, eval x p=0) ∧ eval x t.2≠0 := by
  classical
  let source := PrimeSpectrum.zeroLocus (Set.range q)
  have hs : IsConstructible source := by
    rw [← isConstructible_compl]
    exact (PrimeSpectrum.isRetrocompact_zeroLocus_compl (Set.finite_range q)).isConstructible
      (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
  obtain ⟨S,hS⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr
    (PrimeSpectrum.isConstructible_comap_image (rename_fp (k:=k) c) hs)
  let chart (b : PrimeSpectrum.BasicConstructibleSetData (MvPolynomial I k)) :=
    (Finset.univ.image b.g,b.f)
  refine ⟨S.image chart,fun x => ?_⟩
  rw [lift_projected_closed_point]
  change pointToPoint (k:=k) x ∈ PrimeSpectrum.comap (rename c (R:=k)).toRingHom '' source ↔ _
  rw [←hS]
  have basic (b : PrimeSpectrum.BasicConstructibleSetData (MvPolynomial I k)) :
      pointToPoint (k:=k) x ∈ b.toSet ↔
        (∀ p ∈ (chart b).1, eval x p=0) ∧ eval x (chart b).2≠0 := by
    change (Set.range b.g ⊆ (pointToPoint (k:=k) x).asIdeal ∧
      ¬({b.f} : Set (MvPolynomial I k)) ⊆ (pointToPoint (k:=k) x).asIdeal) ↔ _
    simp [chart,Set.range_subset_iff,Set.singleton_subset_iff,point_mem]
  simpa only [PrimeSpectrum.ConstructibleSetData.toSet,Set.mem_iUnion,Finset.mem_image,
    exists_prop,basic] using
    (show (∃ b ∈ S, (∀ p ∈ (chart b).1, eval x p=0) ∧ eval x (chart b).2≠0) ↔
      ∃ t ∈ S.image chart, (∀ p ∈ t.1, eval x p=0) ∧ eval x t.2≠0 from by
        constructor
        · rintro ⟨b,hb,h⟩; exact ⟨chart b,Finset.mem_image_of_mem _ hb,h⟩
        · rintro ⟨_,ht,h⟩; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ht; exact ⟨b,hb,h⟩)

/-- A single finite family of charts describes the original 8-by-4
tangent compatibility system on complex positions, independently of both
curves. The guard in each chart is required to be nonzero. -/
theorem position_charts :
    ∃ T : Finset (Finset (MvPolynomial Coord ℂ) × MvPolynomial Coord ℂ), ∀ x : GridTuple,
      PositionSystem x ↔ ∃ c ∈ T, (∀ p ∈ c.1, eval x p=0) ∧ eval x c.2≠0 := by
  have zero (s : Slot) : curveEquation 0 0 s=0 := by cases s <;> simp [curveEquation]
  have cut (i : Fin 12) : curveList 0 0 i=0 := zero _
  have eqs : PublishedElimination.equations (List.ofFn edgeList ++ List.ofFn (curveList 0 0)) =
      {y : LiftCoord → ℂ | ∀ i, eval y (edgeList i)=0} := by
    ext y
    change (∀ p ∈ List.ofFn edgeList ++ List.ofFn (curveList 0 0), eval y p=0) ↔ _
    constructor
    · intro h i
      exact h _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
    · intro h p hp
      rcases List.mem_append.mp hp with hp|hp
      · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
        exact h i
      · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
        rw [cut,map_zero]
  have eq := projected_grid_locus 0 0
  rw [eqs] at eq
  obtain ⟨S,hS⟩ := projected_equation_charts (Sum.inl : Coord → LiftCoord) edgeList
  refine ⟨S,fun x => ?_⟩
  rw [←hS]
  have h := Set.ext_iff.mp eq x
  simpa [curveProduct,Function.comp_def] using h.symm

end
end PlanarUnitDistances.Competition.GridElimination
