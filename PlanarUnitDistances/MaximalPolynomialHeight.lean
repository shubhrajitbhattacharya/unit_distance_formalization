import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Polynomial

namespace PlanarUnitDistances.StationaryDeformation
open MvPolynomial
noncomputable section
variable {k : Type*} [Field k]

/-- Every closed point of affine n-space has height n over an arbitrary
field. The residue field may be a nontrivial algebraic extension. -/
theorem maximal_height_fin (n : ℕ) (P : Ideal (MvPolynomial (Fin n) k)) [P.IsMaximal] :
    P.height=n := by
  induction n with
  | zero =>
    let e := MvPolynomial.isEmptyRingEquiv k (Fin 0)
    rw [←e.height_map P,Ideal.eq_bot_of_prime (P.map e),Ideal.height_bot,Nat.cast_zero]
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv k n).toRingEquiv
    let Q := P.map e
    let p := Q.comap Polynomial.C
    let _ : Q.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let _ : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing Q
    let _ : Q.LiesOver p := ⟨rfl⟩
    calc
      P.height = Q.height := (e.height_map P).symm
      _ = p.height+1 := Polynomial.height_eq_height_add_one p Q
      _ = _ := by rw [ih p,Nat.cast_succ]

/-- The actual complementary coordinate index after slicing may be any
finite type, including the empty type. -/
theorem maximal_polynomial_height {ι : Type*} [Fintype ι] (P : Ideal (MvPolynomial ι k)) [P.IsMaximal] :
    P.height=Fintype.card ι := by
  let e := (MvPolynomial.renameEquiv k (Fintype.equivFin ι)).toRingEquiv
  exact (e.height_map P).symm.trans (maximal_height_fin _ (P.map e))

end
end PlanarUnitDistances.StationaryDeformation
