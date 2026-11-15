import PlanarUnitDistances.BivariateCurveCoordinates
import PlanarUnitDistances.GenericDistinctSheets
import PlanarUnitDistances.SmoothCurveTangent

namespace PlanarUnitDistances.SmoothCurveOrders
open BivariateCurveCoordinates OAI.PlanarUnitDistances.BivariateMaps
open MvPolynomial

universe u
variable {k K L : Type u} [Field k] [CharZero k] [IsAlgClosed k] [Field K] [CharZero K]
  [IsAlgClosed K] [Field L] [CharZero L] [Algebra k K] [Algebra K L]
  [Algebra k L] [IsScalarTower k K L]

/-- The private-order conclusion directly for the two original plane
polynomials. No factorization, geometric irreducibility after base change,
smooth sheet or odd valuation is an input. -/
theorem orders_on_plane_curves (f g : MvPolynomial (Fin 2) k) (hf : Irreducible f)
    (hg : Irreducible g) (fd : f.degreeOf 1≠0) (gz : g.degreeOf 0≠0) (gw : g.degreeOf 1≠0)
    (cases : ¬g∣f ∨ 2≤f.degreeOf 1) (z w : L) (hz : Transcendental K z)
    (hzw : aeval ![z,w] f=0) (a b : Fin 4 → K) (ind : AlgebraicIndependent k a)
    (anchors : ∀ i,aeval ![a i,b i] g=0) :
    ∃ M : IntermediateField K L, z ∈ M ∧ w ∈ M ∧ ∃ D : Fin 4 → Mˣ,
      FourRowObstruction.PrivateOrders D ∧ ∀ i,
        let t := (z-algebraMap K L (a i))*(w-algebraMap K L (b i))
        (((D i : M) : L))=t*(t-4) := by
  have alt : ¬encode k g ∣ encode k f ∨ 2≤(encode k f).natDegree := by
    rcases cases with notdiv | hi
    · left
      rintro ⟨v,eq⟩
      apply notdiv
      exact ⟨(encode k).symm v, (encode k).injective (by simpa only [map_mul,AlgEquiv.apply_symm_apply] using eq)⟩
    · right; rwa [vertical_degree]
  apply orders_distinct_or_higher_degree (encode k f) (encode k g)
    (irreducible_bimap _ ((MulEquiv.irreducible_iff (encode k)).mpr hf))
    (by rwa [vertical_degree]) (irreducible_bimap _ ((MulEquiv.irreducible_iff (encode k)).mpr hg))
    (by rwa [vertical_degree]) (by rwa [horizontal_degree]) alt z w hz ?_ a b ind
    (fun i ↦ (encode_eval _ _ _).trans (anchors i))
  rw [encode_map,encode_eval]
  change eval₂ (algebraMap K L) ![z,w] (map (algebraMap k K) f)=0
  rwa [eval₂_map,← IsScalarTower.algebraMap_eq k K L]


end PlanarUnitDistances.SmoothCurveOrders
