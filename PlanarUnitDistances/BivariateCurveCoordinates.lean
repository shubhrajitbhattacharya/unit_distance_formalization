import PlanarUnitDistances.GeometricIrreducibility
import PlanarUnitDistances.GenericBranches

/-! Translation between the two actual position coordinates and the
iterated univariate ring used to choose a smooth sheet. The outer variable
is the ordinate. -/

namespace PlanarUnitDistances.BivariateCurveCoordinates
open OAI.PlanarUnitDistances.BivariateMaps
open Polynomial
noncomputable section

private def first (k : Type*) [Field k] : MvPolynomial (Fin 2) k ≃ₐ[k] k[X][X] :=
  (MvPolynomial.finSuccEquiv k 1).trans (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv k (Fin 1)))

private theorem first_zero {k : Type*} [Field k] :
    first k (MvPolynomial.X 0)=X := by
  change (Polynomial.map _ (MvPolynomial.finSuccEquiv k 1 (MvPolynomial.X 0)))=_
  rw [MvPolynomial.finSuccEquiv_X_zero,Polynomial.map_X]

private theorem first_one {k : Type*} [Field k] :
    first k (MvPolynomial.X 1)=C X := by
  change (Polynomial.map _ (MvPolynomial.finSuccEquiv k 1 (MvPolynomial.X (0:Fin 1).succ)))=_
  rw [MvPolynomial.finSuccEquiv_X_succ,Polynomial.map_C]
  change C (MvPolynomial.eval₂ C (fun _ : Fin 1 ↦ X) (MvPolynomial.X 0))=C X
  rw [MvPolynomial.eval₂_X]

private theorem first_const {k : Type*} [Field k] (c : k) :
    first k (MvPolynomial.C c)=C (C c) := (first k).commutes c

private theorem first_degree {k : Type*} [Field k] (p : MvPolynomial (Fin 2) k) :
    (first k p).natDegree=p.degreeOf 0 := by
  change ((MvPolynomial.finSuccEquiv k 1 p).map (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingHom).natDegree=_
  rw [Polynomial.natDegree_map_eq_of_injective (MvPolynomial.uniqueAlgEquiv k (Fin 1)).injective,
    MvPolynomial.natDegree_finSuccEquiv]

/-- The coordinate `0` is the inner polynomial variable and `1` the outer variable. -/
def encode (k : Type*) [Field k] : MvPolynomial (Fin 2) k ≃ₐ[k] k[X][X] :=
  (first k).trans Bivariate.swap

@[simp] theorem encode_z {k : Type*} [Field k] : encode k (MvPolynomial.X 0)=C X :=
  (congrArg Bivariate.swap first_zero).trans Bivariate.swap_Y
@[simp] theorem encode_w {k : Type*} [Field k] : encode k (MvPolynomial.X 1)=X :=
  (congrArg Bivariate.swap first_one).trans Bivariate.swap_X
@[simp] theorem encode_C {k : Type*} [Field k] (c : k) : encode k (MvPolynomial.C c)=C (C c) :=
  (encode k).commutes c

theorem encode_map {k L : Type*} [Field k] [Field L] (f : k →+* L) (p : MvPolynomial (Fin 2) k) :
    bimap f (encode k p)=encode L (MvPolynomial.map f p) := by
  have h : (bimap f).comp (encode k).toRingHom=(encode L).toRingHom.comp (MvPolynomial.map f) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [OAI.PlanarUnitDistances.BivariateMaps.bimap]
    · intro i; fin_cases i <;> simp [OAI.PlanarUnitDistances.BivariateMaps.bimap]
  exact RingHom.congr_fun h p

theorem vertical_degree {k : Type*} [Field k] (p : MvPolynomial (Fin 2) k) :
    (encode k p).natDegree=p.degreeOf 1 := by
  let s := Equiv.swap (0:Fin 2) 1
  have h : (encode k).toRingHom=(first k).toRingHom.comp (MvPolynomial.rename s).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [first_const]
    · intro i; fin_cases i <;> simp [s,first_one,first_zero]
  calc
    (encode k p).natDegree = (first k (MvPolynomial.rename s p)).natDegree := congrArg Polynomial.natDegree (RingHom.congr_fun h p)
    _ = (MvPolynomial.rename s p).degreeOf 0 := first_degree _
    _ = p.degreeOf 1 := by simpa [s] using MvPolynomial.degreeOf_rename_of_injective (p:=p) s.injective 1

theorem horizontal_degree {k : Type*} [Field k] (p : MvPolynomial (Fin 2) k) :
    (Bivariate.swap (encode k p)).natDegree=p.degreeOf 0 := by
  change (Bivariate.swap (Bivariate.swap (first k p))).natDegree=_
  rw [Bivariate.swap_swap_apply,first_degree]

theorem encode_eval {k L : Type*} [Field k] [Field L] [Algebra k L] (p : MvPolynomial (Fin 2) k)
    (a b : L) : (encode k p).eval₂ (aeval a).toRingHom b=MvPolynomial.aeval ![a,b] p := by
  have h : (eval₂RingHom (aeval a).toRingHom b).comp (encode k).toRingHom=
      (MvPolynomial.aeval ![a,b]).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro i; fin_cases i <;> simp
  exact RingHom.congr_fun h p

/-- Absolute irreducibility in the sheet presentation, obtained by descent
of hypothetical factors preserving their monomial supports. -/
theorem irreducible_bimap {k L : Type*} [Field k] [IsAlgClosed k] [Field L] [Algebra k L]
    (f : k[X][X]) (hf : Irreducible f) : Irreducible (bimap (algebraMap k L) f) := by
  let p := (encode k).symm f
  have hp : Irreducible p := (MulEquiv.irreducible_iff (encode k).symm).mpr hf
  have h := (MulEquiv.irreducible_iff (encode L)).mpr (GeometricIrreducibility.irreducible_map p hp)
  rwa [← encode_map,show encode k p=f from (encode k).apply_symm_apply f] at h

end
end PlanarUnitDistances.BivariateCurveCoordinates
