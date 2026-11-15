import PlanarUnitDistances.IntegralMacaulayDeformation
import PlanarUnitDistances.ReducedDeformation

namespace PlanarUnitDistances.MacaulayFactorBounds
open HomogeneousMacaulay BlockMacaulay EliminantHeight MvPolynomial Finset
open scoped Classical
noncomputable section

private def tower {σ : Type*} : MvPolynomial (Option (Option σ)) ℤ →+*
    Polynomial (Polynomial (MvPolynomial σ ℤ)) :=
  (Polynomial.mapRingHom (optionEquivLeft ℤ σ).toRingHom).comp
    (optionEquivLeft ℤ (Option σ)).toRingHom

private theorem tower_X_none {σ : Type*} :
    tower (σ:=σ) (X none) = Polynomial.X := by simp [tower]

private theorem tower_X_some_none {σ : Type*} :
    tower (σ:=σ) (X (some none)) = Polynomial.C Polynomial.X := by simp [tower]

private theorem tower_X_some_some {σ : Type*} (s : σ) :
    tower (X (some (some s))) = Polynomial.C (Polynomial.C (X s)) := by simp [tower]

private theorem tower_coeff {σ : Type*} (p : MvPolynomial (Option (Option σ)) ℤ) (j : ℕ) :
    (tower p).coeff j = optionEquivLeft ℤ σ ((optionEquivLeft ℤ (Option σ) p).coeff j) := by
  simp [tower, Polynomial.coeff_map]

/-- This is precisely the nested polynomial used in deformation, with integer generic
    input coefficients and the same ε and T ordering. -/
theorem tower_deformation {q : ℕ} (F : Universal q) :
    tower (F.eval₂ C genericDeformedEntry) =
      UniversalIncidence.deformationMap (fun i m => (X ⟨i,m⟩ : Universal q)) F := by
  let A : Coefficients q (Universal q) := fun i m => X ⟨i,m⟩
  have hom : tower.comp (eval₂Hom C genericDeformedEntry) = UniversalIncidence.deformationMap A := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [tower, UniversalIncidence.deformationMap]
    · intro e
      simp only [RingHom.comp_apply, UniversalIncidence.deformationMap, eval₂Hom_X']
      obtain ⟨i,m⟩ := e
      by_cases hm : m = pureMon i (formDegree i)
      · cases i <;> simp [genericDeformedEntry, deformed, monomialSystem, A, hm,
          tower_X_none, tower_X_some_none, tower_X_some_some]
      · cases i <;> simp [genericDeformedEntry, deformed, monomialSystem, A, hm,
          tower_X_none, tower_X_some_none, tower_X_some_some]
  exact congrArg (fun f => (f : Universal q →+* _) F) hom

private theorem option_coefficient_sum {σ : Type*} (f : MvPolynomial (Option σ) ℤ) (j : ℕ) :
    coefficientSum ((optionEquivLeft ℤ σ f).coeff j) ≤ coefficientSum f := by
  classical
  let T := ((optionEquivLeft ℤ σ f).coeff j).support
  let g (d : σ →₀ ℕ) := d.optionElim j
  have injective : Function.Injective g := fun a b eq => by
    simpa only [g, Finsupp.some_optionElim] using congrArg Finsupp.some eq
  have sub : T.image g ⊆ f.support := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    have hs := MvPolynomial.mem_support_iff.mp hb
    rw [optionEquivLeft_coeff_coeff] at hs
    exact MvPolynomial.mem_support_iff.mpr hs
  have h := sum_le_sum_of_subset_of_nonneg (f:=fun a => (f.coeff a).natAbs) sub (by intros; omega)
  rw [sum_image (fun _ _ _ _ h => injective h)] at h
  simpa only [coefficientSum, optionEquivLeft_coeff_coeff, T, g] using h

/-- Every coefficient after selecting arbitrary T and ε powers is an integral polynomial
    in the initial input coefficients with the proven total degree and coefficient sum. -/
theorem deformation_coefficient_bounds {q : ℕ} (hq : q ≤ 98) (F : Universal q)
    (divides : ∀ i, F ∣ minor i) (j k : ℕ) :
    let A : Coefficients q (Universal q) := fun i m => X ⟨i,m⟩
    let Cjk := (((UniversalIncidence.deformationMap A F).coeff j).coeff k)
    Cjk.totalDegree < 2^104 ∧ coefficientSum Cjk ≤ 2^(2^401) := by
  dsimp only
  rw [←tower_deformation, tower_coeff]
  let f := F.eval₂ C genericDeformedEntry
  let g := ((optionEquivLeft ℤ (Option (Parameter q))) f).coeff j
  change ((((optionEquivLeft ℤ (Parameter q)) g).coeff k).totalDegree < _) ∧
    coefficientSum (((optionEquivLeft ℤ (Parameter q)) g).coeff k) ≤ _
  exact ⟨(totalDegree_coeff_optionEquivLeft_le ..).trans
      ((totalDegree_coeff_optionEquivLeft_le ..).trans (generic_deformation_degree F))
      |>.trans_lt (degree_budget divides hq),
    (option_coefficient_sum g k).trans ((option_coefficient_sum f j).trans (generic_deformation_size hq F divides))⟩

theorem swap_coeff_coeff {R : Type*} [CommSemiring R] (P : Polynomial (Polynomial R)) (j k : ℕ) :
    (((Polynomial.Bivariate.swap P).coeff k).coeff j) = (P.coeff j).coeff k := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | monomial a c =>
    induction c using Polynomial.induction_on' with
    | add f g hf hg => simp only [map_add, Polynomial.coeff_add, hf, hg]
    | monomial b r =>
      rw [Polynomial.Bivariate.swap_monomial_monomial]
      by_cases h : a=j <;> by_cases h' : b=k <;> simp [Polynomial.coeff_monomial, h, h']

/-- Mapping the initial coefficients of the nested elimination polynomial commutes with
    the two-parameter deformation without rescaling any coefficient. -/
theorem map_deformation {q : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Coefficients q R) (F : Universal q) :
    (UniversalIncidence.deformationMap A F).map (Polynomial.mapRingHom f) =
      UniversalIncidence.deformationMap (fun i m => f (A i m)) F := by
  let Φ := Polynomial.mapRingHom (Polynomial.mapRingHom f)
  have e : Φ.comp (UniversalIncidence.deformationMap A) =
      UniversalIncidence.deformationMap (fun i m => f (A i m)) := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [Φ, UniversalIncidence.deformationMap]
    · intro v
      simp only [RingHom.comp_apply, UniversalIncidence.deformationMap, eval₂Hom_X']
      rw [map_deformed]
      simp [Φ]
  exact congrArg (fun g => (g : Universal q →+* _) F) e

/-- Every specialized coefficient of the swapped relation comes from an integral form
    with explicit bounds. The indices may be chosen after the input system is fixed. -/
theorem specialized_swapped_coefficient {q : ℕ} (hq : q ≤ 98) (F : Universal q)
    (divides : ∀ i, F ∣ minor i) (j k : ℕ) :
    ∃ G : Universal q, G.totalDegree < 2^104 ∧ coefficientSum G ≤ 2^(2^401) ∧
      ∀ {R : Type*} [CommRing R] (A : Coefficients q R),
        ((Polynomial.Bivariate.swap (UniversalIncidence.deformationMap A F)).coeff k).coeff j =
          eval₂Hom (Int.castRingHom R) (fun e : Parameter q => A e.1 e.2) G := by
  let U : Coefficients q (Universal q) := fun i m => X ⟨i,m⟩
  let G := ((UniversalIncidence.deformationMap U F).coeff j).coeff k
  have h := deformation_coefficient_bounds hq F divides j k
  refine ⟨G, h.1, h.2, ?_⟩
  intro R _ A
  let φ := eval₂Hom (Int.castRingHom R) (fun e : Parameter q => A e.1 e.2)
  have e : (fun i m => φ (U i m)) = A := by funext i m; simp [φ,U]
  have hmap := map_deformation φ U F
  rw [e] at hmap
  rw [swap_coeff_coeff, ←hmap, Polynomial.coeff_map]
  exact Polynomial.coeff_map φ _

end
end PlanarUnitDistances.MacaulayFactorBounds
