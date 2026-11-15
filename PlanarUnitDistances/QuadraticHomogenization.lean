import PlanarUnitDistances.IsolatedCoordinateEliminant
import Mathlib.Data.Finsupp.Option

namespace PlanarUnitDistances.UniversalIncidence
open HomogeneousMacaulay MvPolynomial Finset
noncomputable section
variable {q : ℕ} {k : Type*} [Field k]

def padQuadratic (d : Fin q →₀ ℕ) : Coord q →₀ ℕ :=
  Finsupp.single none (2-d.degree)+d.embDomain .some

@[simp] theorem padQuadratic_some (d : Fin q →₀ ℕ) : (padQuadratic d).some=d := by
  simp only [padQuadratic,Finsupp.some_add,Finsupp.some_single_none,Finsupp.some_embDomain_some,zero_add]

def quadraticHomogenization (p : State q k) : MvPolynomial (Coord q) k :=
  ∑d ∈ p.support,monomial (padQuadratic d) (p.coeff d)

theorem quadraticHomogenization_homogeneous (p : State q k) (deg : p.totalDegree≤2) :
    (quadraticHomogenization p).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro d hd
  have h : d.degree≤2 := (le_totalDegree hd).trans deg
  apply isHomogeneous_monomial
  rw [padQuadratic,map_add,Finsupp.degree_single,Finsupp.embDomain_eq_mapDomain,Finsupp.degree_mapDomain]
  exact Nat.sub_add_cancel h

private theorem dehom_rename (p : State q k) : dehom (rename Option.some p)=p := by
  rw [dehom,eval₂Hom_rename]
  change eval₂Hom C X p=p
  simp

theorem dehom_quadraticHomogenization (p : State q k) : dehom (quadraticHomogenization p)=p := by
  refine Eq.trans ?_ p.support_sum_monomial_coeff
  rw [quadraticHomogenization,map_sum]
  apply sum_congr rfl
  intro d _
  have term : monomial (padQuadratic d) (p.coeff d)=
      X none^(2-d.degree)*rename Option.some (monomial d (p.coeff d)) := by
    simp [padQuadratic,X_pow_eq_monomial,rename_monomial,monomial_mul_monomial,Finsupp.embDomain_eq_mapDomain]
  rw [term,map_mul,map_pow,dehom_rename]
  simp [dehom]

/-- Homogenization leaves each coefficient unchanged and inserts only
zeros in the remaining monomial slots. -/
theorem coeff_quadraticHomogenization (p : State q k) (m : Coord q →₀ ℕ) :
    (quadraticHomogenization p).coeff m=if padQuadratic m.some=m then p.coeff m.some else 0 := by
  classical
  have equal {d : Fin q →₀ ℕ} (h : padQuadratic d=m) : d=m.some := by
    simpa only [padQuadratic_some] using congrArg Finsupp.some h
  rw [quadraticHomogenization,coeff_sum]
  by_cases h : padQuadratic m.some=m
  · rw [ite_eq_left h,Finset.sum_eq_single m.some]
    · simp [coeff_monomial,h]
    · intro d _ hd
      have hn : padQuadratic d≠m := fun e => hd (equal e)
      simp [coeff_monomial,hn]
    · intro hs
      simp [notMem_support_iff.mp hs]
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro d _
    have hn : padQuadratic d≠m := fun e => h ((congrArg padQuadratic (equal e)).symm.trans e)
    simp [coeff_monomial,hn]

theorem coeff_quadratic_slot (p : State q k) (m : Mon q 2) :
    (quadraticHomogenization p).coeff m.val=p.coeff m.val.some := by
  have sum : m.val none+m.val.some.degree=2 := by
    simpa [Fintype.sum_option,Finsupp.degree_eq_sum] using sum_exponents m
  have pad : padQuadratic m.val.some=m.val := by
    ext o
    cases o with
    | none => simp [padQuadratic];omega
    | some i => simp [padQuadratic]
  simp [coeff_quadraticHomogenization,pad]

theorem input_test_slot (j : Fin q) (Q : Fin q → MvPolynomial (Coord q) k) (m : Mon q 1) :
    inputCoefficients j Q none m=if Finsupp.single (some j) 1=m.val then 1 else 0 :=
  coeff_X (some j) m.val

theorem input_quadratic_slot (j i : Fin q) (g : Fin q → State q k) (m : Mon q 2) :
    inputCoefficients j (fun t => quadraticHomogenization (g t)) (some i) m=(g i).coeff m.val.some :=
  coeff_quadratic_slot _ _

/-- Literal affine equations of degree at most two, including constants
and equations of smaller degree. Each coefficient supplied to F is the
original coefficient of the affine equation in its matching monomial. -/
theorem affine_coordinate_from_relation {q : ℕ} (F : BlockMacaulay.Universal q)
    (rel : incidenceMap F=0) (divides : F ∣ universalDeterminant q) (k : Type) [Field k] (j : Fin q)
    (g : Fin q → State q k) (deg : ∀i,(g i).totalDegree≤2) :
    let H := Polynomial.Bivariate.swap (deformationMap
      (inputCoefficients j (fun i => quadraticHomogenization (g i))) F)
    H≠0 ∧ ∃ d, H.coeff d≠0 ∧ (∀ e<d,H.coeff e=0) ∧
      ∀ (M : Ideal (State q k)) [M.IsMaximal], M ∈ (Ideal.span (Set.range g)).minimalPrimes →
        outputTest j (H.coeff d)∈M ∧ ∀c : k,X j-C c∈M → (H.coeff d).IsRoot c := by
  simpa only [dehom_quadraticHomogenization] using
    isolated_coordinate_from_relation F rel divides k j (fun i => quadraticHomogenization (g i))
      (fun i => quadraticHomogenization_homogeneous _ (deg i))


end
end PlanarUnitDistances.UniversalIncidence
