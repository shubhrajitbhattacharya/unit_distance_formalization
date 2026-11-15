import PlanarUnitDistances.GenericBranches
import PlanarUnitDistances.ChordObstruction

/-! Private orders for a generic row on a non-rational plane curve. The
coefficient field for the four radicands embeds inside the particular
solution field in which the row and its labels have been supplied. -/

noncomputable section

namespace PlanarUnitDistances.SmoothCurveOrders

open Polynomial OAI.PlanarUnitDistances
open CurveValuations BivariateMaps FourRowObstruction
open scoped WithZero

private def orderOfValuation {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰) :
    Fˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (-WithZero.log (v (x : F)))
  map_one' := by simp
  map_mul' x y := by
    simp only [Units.val_mul,map_mul]
    rw [WithZero.log_mul (by simp [x.ne_zero]) (by simp [y.ne_zero]),neg_add]
    rfl

/-- Smooth private sheets on a given curve yield orders on the actual
embedded function field. Its abscissa and ordinate are the specified
elements `z,w` of `L`. -/
theorem embedded_orders_of_sheets {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
    (f : K[X][X]) (hf : Irreducible f) (hd : f.natDegree≠0)
    (z w : L) (hz : Transcendental K z) (hzw : f.eval₂ (aeval z).toRingHom w=0)
    (a b : Fin 4 → K)
    (sheets : ∀ i, ∃ c : K, f.leadingCoeff.eval (a i)≠0 ∧
      f.eval₂ (evalRingHom (a i)) c=0 ∧ f.derivative.eval₂ (evalRingHom (a i)) c≠0 ∧
      c≠b i ∧ ∀ j, j≠i → (a i-a j)*(c-b j)≠0 ∧ (a i-a j)*(c-b j)≠4) :
    ∃ M : IntermediateField K L, z ∈ M ∧ w ∈ M ∧ ∃ D : Fin 4 → Mˣ,
      PrivateOrders D ∧ ∀ i, let t := (z-algebraMap K L (a i))*(w-algebraMap K L (b i))
                            (((D i : M) : L))=t*(t-4) := by
  letI : Fact (Irreducible (f.map (algebraMap K[X] (RatFunc K)))) :=
    ⟨GenericCurve.irreducible_fraction_curve f hf hd⟩
  obtain ⟨φ,_,hw,hpoly⟩ := GenericCurve.exists_curve_embedding f hf hd z w hz hzw
  have hx : φ (curveZ f)=z := by simpa only [curveZ,aeval_X] using hpoly X
  have hc (x : K) : φ (curveC f x)=algebraMap K L x := by
    simpa only [curveC,aeval_C] using hpoly (C x)
  have valuations (i : Fin 4) : ∃ v : Valuation (CurveField f) ℤᵐ⁰,
      v (curveD f (a i) (b i))=WithZero.exp (-1:ℤ) ∧
      ∀ j, j≠i → v (curveD f (a j) (b j))=1 := by
    obtain ⟨c,lead,root,ds,bc,away⟩ := sheets i
    obtain ⟨v,one,rest⟩ := exists_curve_private_valuation f (a i) c (b i) lead root ds bc
    exact ⟨v,one,fun j neq ↦ rest _ _ (away j neq).1 (away j neq).2⟩
  choose v hv hv' using valuations
  let e := φ.equivFieldRange
  let d i := curveD f (a i) (b i)
  have dn i : d i≠0 := by
    intro h
    have ve := hv i
    change v i (d i)=_ at ve
    rw [h,map_zero] at ve
    exact WithZero.exp_ne_zero ve.symm
  let D (i : Fin 4) : φ.fieldRangeˣ := Units.mk0 (e (d i)) (by simpa using dn i)
  refine ⟨φ.fieldRange, ⟨_,hx⟩, ⟨_,hw⟩, D, ?_, ?_⟩
  · intro i
    let v' := (v i).comap e.symm.toRingHom
    refine ⟨orderOfValuation v',?_,?_⟩
    · change -WithZero.log (v i (e.symm (e (d i))))=1
      simp [d,hv]
    · intro j hj
      change -WithZero.log (v i (e.symm (e (d j)) ))=0
      simp [d,hv' i j hj]
  · intro i
    change φ (curveD f (a i) (b i))=_
    simp only [curveD,curveL,map_mul,map_sub,map_ofNat,hx,hw,hc]

/-- The sheets and their simple, private intersections follow from the
generic four anchor abscissas and the original two curve equations. The
last disjunction excludes exactly the common degree-one sheet. -/
theorem smooth_curve_orders {B K L : Type*} [Field B] [CharZero B] [Field K] [CharZero K]
    [IsAlgClosed K] [Field L] [Algebra B K] [Algebra K L]
    (f g : B[X][X]) (hf : Irreducible (bimap (algebraMap B K) f)) (hd : f.natDegree≠0)
    (hg : Irreducible (bimap (algebraMap B K) g)) (hgs : (Bivariate.swap g).natDegree≠0)
    (z w : L) (hz : Transcendental K z)
    (hzw : (bimap (algebraMap B K) f).eval₂ (aeval z).toRingHom w=0)
    (a b : Fin 4 → K) (ha : AlgebraicIndependent B a)
    (hb : ∀ i, g.eval₂ (aeval (a i)).toRingHom (b i)=0)
    (cases : ∀ i, f.eval₂ (aeval (a i)).toRingHom (b i)≠0 ∨ 2≤f.natDegree) :
    ∃ M : IntermediateField K L, z ∈ M ∧ w ∈ M ∧ ∃ D : Fin 4 → Mˣ,
      PrivateOrders D ∧ ∀ i, let t := (z-algebraMap K L (a i))*(w-algebraMap K L (b i))
                            (((D i : M) : L))=t*(t-4) := by
  apply embedded_orders_of_sheets _ hf (by simpa only [bimap_natDegree] using hd) z w hz hzw a b
  intro i
  have hbase := irreducible_of_bimap (algebraMap B K) hf
  obtain ⟨c,hr,dr,bc,rest⟩ := GenericSheets.exists_private_sheet_curve f g hbase hd hg hgs
    a b ha hb i (cases i)
  refine ⟨c,?_,?_,?_,bc,rest⟩
  · rw [GenericSheets.mapped_leading_eval]
    exact GenericCurve.fiber_leadingCoeff_ne_zero f hbase.ne_zero (a i) (ha.transcendental i)
  · simpa only [GenericSheets.mapped_eval] using hr
  · simpa only [GenericSheets.mapped_derivative_eval] using dr

end PlanarUnitDistances.SmoothCurveOrders
