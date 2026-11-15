import PlanarUnitDistances.SmoothCurveOrders

namespace PlanarUnitDistances.SmoothCurveOrders
open Polynomial OAI.PlanarUnitDistances OAI.PlanarUnitDistances.BivariateMaps

/-- An abscissa transcendental over the coefficients detects the entire
irreducible curve. Vanishing of another equation at the chosen branch
point forces divisibility in the original bivariate polynomial ring. -/
theorem divides_of_transcendental_common_zero {B K : Type*} [Field B] [Field K] [Algebra B K]
    (g f : B[X][X]) (hg : Irreducible g) (dg : g.natDegree ≠ 0)
    (a b : K) (ha : Transcendental B a)
    (rootg : g.eval₂ (aeval a).toRingHom b=0) (rootf : f.eval₂ (aeval a).toRingHom b=0) :
    g ∣ f := by
  let j := algebraMap B[X] (RatFunc B)
  let φ := eval₂RingHom (GenericCurve.ratEval a ha).toRingHom b
  have van (h : B[X][X]) (hr : h.eval₂ (aeval a).toRingHom b=0) : φ (h.map j)=0 := by
    change (h.map (algebraMap B[X] (RatFunc B))).eval₂ (GenericCurve.ratEval a ha).toRingHom b=0
    rwa [eval₂_map,GenericCurve.ratEval_comp]
  apply ((hg.isPrimitive dg).dvd_iff_fraction_map_dvd_fraction_map (RatFunc B)).mpr
  apply (GenericCurve.irreducible_fraction_curve g hg dg).dvd_iff_not_isCoprime.mpr
  rintro ⟨p,q,bez⟩
  have eq := congrArg φ bez
  simp only [map_add,map_mul,map_one] at eq
  change φ p*φ (g.map j)+φ q*φ (f.map j)=1 at eq
  rw [van g rootg,van f rootf,mul_zero,mul_zero,add_zero] at eq
  exact zero_ne_one eq

/-- In the distinct-curve case, all four alternative-sheet hypotheses are
consequences of nondivisibility on the coefficient field. The same conclusion
holds for a row curve of vertical degree at least two, including `f=g`. -/
theorem orders_distinct_or_higher_degree {B K L : Type*} [Field B] [CharZero B]
    [Field K] [CharZero K] [IsAlgClosed K] [Field L] [Algebra B K] [Algebra K L]
    (f g : B[X][X]) (hf : Irreducible (bimap (algebraMap B K) f)) (hd : f.natDegree≠0)
    (hg : Irreducible (bimap (algebraMap B K) g)) (hgd : g.natDegree≠0)
    (hgs : (Bivariate.swap g).natDegree≠0) (cases : ¬g∣f ∨ 2≤f.natDegree)
    (z w : L) (hz : Transcendental K z)
    (hzw : (bimap (algebraMap B K) f).eval₂ (aeval z).toRingHom w=0)
    (a b : Fin 4 → K) (ha : AlgebraicIndependent B a)
    (hb : ∀ i,g.eval₂ (aeval (a i)).toRingHom (b i)=0) :
    ∃ M : IntermediateField K L, z ∈ M ∧ w ∈ M ∧ ∃ D : Fin 4 → Mˣ,
      FourRowObstruction.PrivateOrders D ∧ ∀ i,
        let t := (z-algebraMap K L (a i))*(w-algebraMap K L (b i))
        (((D i : M) : L))=t*(t-4) := by
  apply smooth_curve_orders f g hf hd hg hgs z w hz hzw a b ha hb
  intro i
  rcases cases with ndiv | deg
  · exact Or.inl (fun vanish ↦ ndiv (divides_of_transcendental_common_zero g f
      (irreducible_of_bimap _ hg) hgd _ _ (ha.transcendental i) (hb i) vanish))
  · exact Or.inr deg

end PlanarUnitDistances.SmoothCurveOrders
