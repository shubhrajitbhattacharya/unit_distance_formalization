import PlanarUnitDistances.IncidenceFaithfulness
import PlanarUnitDistances.UniversalIncidenceFactor
import PlanarUnitDistances.BlockMacaulay

namespace PlanarUnitDistances.UniversalIncidence
open HomogeneousMacaulay MvPolynomial Finset
open scoped Classical
noncomputable section
variable {q : ℕ}

def constantMon (i : Coord q) : Mon q (formDegree i) := pureMon none (formDegree i)
abbrev OffConstant (i : Coord q) := {m : Mon q (formDegree i) // m ≠ constantMon i}
abbrev FreeCoeff (q : ℕ) := Σ i : Coord q, OffConstant i
abbrev IncidenceRing (q : ℕ) := ChartRing ℤ (FreeCoeff q) (Fin q)

def affinePoint : Coord q → IncidenceRing q
  | none => 1
  | some j => X (.inr j)

def ambientMonomial (d : Coord q →₀ ℕ) : IncidenceRing q :=
  d.prod (fun i n => affinePoint i ^ n)

def reconstruct (i : Coord q) : IncidenceRing q :=
  -∑ m : OffConstant i, X (.inl ⟨i,m⟩)*ambientMonomial m.val.val

def diagonalValue (s : FreeCoeff q) : ℤ :=
  if s.2.val=pureMon s.1 (formDegree s.1) then -1 else 0


private def squareIndex (j : Fin q) : OffConstant (some j) :=
  ⟨pureMon (some j) 2,by
    intro h
    have same := congrArg (fun m : Mon q 2 => m.val (some j)) h
    simp [pureMon,constantMon] at same⟩

theorem actual_diagonal (j : Fin q) : center diagonalValue (reconstruct (some j))=X (.inr j)^2 := by
  rw [reconstruct,map_neg,map_sum,Finset.sum_eq_single (squareIndex j)]
  · simp [map_mul,center,diagonalValue,squareIndex,pureMon,ambientMonomial,
      Finsupp.prod_single_index,affinePoint,formDegree]
  · intro m _ hm
    have h : m.val ≠ pureMon (some j) 2 := fun e => hm (Subtype.ext e)
    have hv : diagonalValue (⟨some j,m⟩ : FreeCoeff q)=0 := ite_eq_right h
    simp only [map_mul,center,eval₂Hom_X',Sum.elim_inl,hv,map_zero,zero_mul]
  · simp

theorem remaining_coefficients_faithful :
    Function.Injective (chartMap (fun j : Fin q => reconstruct (some j))) :=
  chart_faithful _ diagonalValue actual_diagonal

/-- All universal coefficients on the affine incidence parametrization,
in which the coefficient of x₀^d is solved from each input equation. -/
def affineCoefficients : Coefficients q (IncidenceRing q) := fun i m =>
  if h : m=constantMon i then reconstruct i else X (.inl ⟨i,⟨m,h⟩⟩)

private def monAt {R : Type*} [CommRing R] (x : Fin q → R) (d : Coord q →₀ ℕ) : R :=
  d.prod (fun i n => i.elim 1 x ^ n)

private theorem affine_value {R : Type*} [CommRing R] (x : Fin q → R) (A : Coefficients q R)
    (i : Coord q) : eval (fun j : Coord q => j.elim 1 x) (form A i) =
      (∑ m : OffConstant i, A i m.val*monAt x m.val.val)+A i (constantMon i) := by
  unfold form
  simp only [map_sum,map_mul,eval_C,eval_monomial,one_mul]
  change (∑ m : Mon q (formDegree i), A i m*monAt x m.val)=_
  rw [←sum_erase_add univ _ (mem_univ (constantMon i))]
  have const : monAt x (constantMon i).val=1 := by
    simp [monAt,constantMon,pureMon,Finsupp.prod_single_index]
  rw [const,mul_one]
  rw [Finset.sum_subtype (p:=fun m => m≠constantMon i) (univ.erase (constantMon i)) (fun _ => by simp)]

theorem affine_common_zero (i : Coord q) : eval affinePoint (form affineCoefficients i)=0 := by
  let x (j : Fin q) : IncidenceRing q := X (.inr j)
  have ea : affinePoint = (fun j : Coord q => j.elim 1 x) := by funext j; cases j <;> rfl
  have ma (s : Coord q →₀ ℕ) : monAt x s=ambientMonomial s := by
    simp only [monAt,ambientMonomial,ea]
  rw [ea,affine_value]
  have free (m : OffConstant i) : affineCoefficients i m.val=X (.inl ⟨i,m⟩) := dite_eq_right m.property
  simp only [ma,free]
  simp [affineCoefficients,reconstruct]

def incidenceMap : BlockMacaulay.Universal q →+* IncidenceRing q :=
  eval₂Hom (Int.castRingHom _) (fun e => affineCoefficients e.1 e.2)

theorem minor_in_kernel (ℓ : Coord q) : incidenceMap (BlockMacaulay.minor ℓ)=0 := by
  rw [incidenceMap,BlockMacaulay.eval_minor]
  apply BlockMacaulay.common_zero ℓ _ affinePoint ⟨none,one_ne_zero⟩ affine_common_zero

/-- Every relation in this kernel vanishes at the coefficients of every
actual homogeneous system with a common root whose first coordinate is one. -/
theorem specializes_at_affine_point {R : Type*} [CommRing R] (A : Coefficients q R) (x : Fin q → R)
    (root : ∀i,eval (fun j : Coord q => j.elim 1 x) (form A i)=0)
    (F : BlockMacaulay.Universal q) (relation : incidenceMap F=0) :
    eval₂Hom (Int.castRingHom R) (fun e : Parameter q => A e.1 e.2) F=0 := by
  let ψ : IncidenceRing q →+* R := eval₂Hom (Int.castRingHom R)
    (Sum.elim (fun e : FreeCoeff q => A e.1 e.2.val) x)
  have point (j : Coord q) : ψ (affinePoint j)=j.elim 1 x := by cases j <;> simp [affinePoint,ψ]
  have mon (s : Coord q →₀ ℕ) : ψ (ambientMonomial s)=monAt x s := by
    simp [ambientMonomial,monAt,Finsupp.prod,point]
  have recovered (i : Coord q) : ψ (reconstruct i)=A i (constantMon i) := by
    have hz := root i
    rw [affine_value] at hz
    simp only [reconstruct,map_neg,map_sum,map_mul,mon]
    simpa [ψ] using (neg_eq_of_add_eq_zero_right hz)
  have commutes : ψ.comp incidenceMap = eval₂Hom (Int.castRingHom R) (fun e : Parameter q => A e.1 e.2) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [incidenceMap,ψ]
    · rintro ⟨i,m⟩
      by_cases h : m=constantMon i
      · subst m
        simp [incidenceMap,affineCoefficients,recovered]
      · simp [incidenceMap,affineCoefficients,h,ψ]
  rw [←commutes]
  exact (congrArg ψ relation).trans (map_zero _)

/-- Split off the linear form's constant coefficient. Every remaining
quadratic constant is represented by its index in Fin q. -/
def parameterEquiv (q : ℕ) : Parameter q ≃ Option (FreeCoeff q ⊕ Fin q) where
  toFun e := if h : e.2=constantMon e.1 then e.1.map Sum.inr
    else some (.inl ⟨e.1,⟨e.2,h⟩⟩)
  invFun
    | none => ⟨none,constantMon none⟩
    | some (.inl a) => ⟨a.1,a.2.val⟩
    | some (.inr j) => ⟨some j,constantMon (some j)⟩
  left_inv := by
    rintro ⟨i,m⟩
    cases i with
    | none => by_cases h : m=constantMon (none : Coord q) <;> simp [h]
    | some j => by_cases h : m=constantMon (some j) <;> simp [h]
  right_inv := by
    rintro (_|s)
    · simp
    · rcases s with ⟨i,⟨m,h⟩⟩|j <;> simp_all

def parameterPolynomial (q : ℕ) :
    BlockMacaulay.Universal q ≃ₐ[ℤ] Polynomial (IncidenceRing q) :=
  (MvPolynomial.renameEquiv ℤ (parameterEquiv q)).trans (MvPolynomial.optionEquivLeft ℤ _)

private theorem coefficient_hom :
    (incidenceMap (q:=q)).comp ((parameterPolynomial q).symm.toRingHom.comp Polynomial.C) =
      chartMap (fun j : Fin q => reconstruct (some j)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [parameterPolynomial,incidenceMap,chartMap]
  · rintro (⟨i,⟨m,h⟩⟩|j) <;>
      simp_all [parameterPolynomial,parameterEquiv,incidenceMap,affineCoefficients,chartMap]

/-- A single nonzero integral relation for the full affine incidence
family divides every distinguished-block minor. This detects incidence at
x₀=1 even when the common zero is singular or belongs to a component. -/
theorem exists_incidence_relation (q : ℕ) :
    ∃ F : BlockMacaulay.Universal q, F≠0 ∧ incidenceMap F=0 ∧
      (∀ G : BlockMacaulay.Universal q, incidenceMap G=0 ↔ F ∣ G) ∧
      F.totalDegree≤2^q+q*2^(q-1) := by
  let e := parameterPolynomial q
  let φ := (incidenceMap (q:=q)).comp e.symm.toRingHom
  have faithful : Function.Injective (φ.comp Polynomial.C) := by
    change Function.Injective ((incidenceMap (q:=q)).comp (e.symm.toRingHom.comp Polynomial.C))
    rw [coefficient_hom]
    exact remaining_coefficients_faithful
  let w := e (BlockMacaulay.minor (none : Coord q))
  have nw : w≠0 := by
    intro h
    exact BlockMacaulay.minor_ne_zero none (e.injective (by simpa [w] using h))
  have zw : φ w=0 := by simpa [φ,w] using minor_in_kernel (none : Coord q)
  obtain ⟨p,np,zp,univ⟩ := exists_common_relation φ faithful w nw zw
  let F := e.symm p
  have nf : F≠0 := by
    intro h
    exact np (by simpa [F] using congrArg e h)
  have all (G : BlockMacaulay.Universal q) : incidenceMap G=0 ↔ F ∣ G := by
    have agree : φ (e G)=incidenceMap G := by simp [φ]
    rw [←agree,univ]
    constructor
    · intro h
      simpa [F] using map_dvd e.symm h
    · intro h
      simpa [F] using map_dvd e h
  exact ⟨F,nf,zp,all,BlockMacaulay.totalDegree_of_common_divisor (fun ℓ => (all _).mp (minor_in_kernel ℓ))⟩


end
end PlanarUnitDistances.UniversalIncidence
