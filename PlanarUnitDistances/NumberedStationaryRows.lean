import PlanarUnitDistances.HonestMacaulayTable
import PlanarUnitDistances.NumberedCoordinateSlice

namespace PlanarUnitDistances.IntegralGrid
open CriticalLocus MvPolynomial TorusCritical
noncomputable section
variable {I J k : Type} [Fintype I] [Fintype J] [Field k] {r w : ℕ}

def orderedOriginal (a : I → Option J → kˣ) (i : I) (j : Option J)
    (pick : Fin r → Equation I J) (ord : Input I J r ≃ Fin w) (t : Fin w) :
    MvPolynomial (Slots I J r) k :=
  incidenceEquation (TorusCritical.ratio a i j) ((TorusCritical.equation a) ∘ pick) id (ord.symm t)

theorem span_orderedOriginal (a : I → Option J → kˣ) (i : I) (j : Option J)
    (pick : Fin r → Equation I J) (ord : Input I J r ≃ Fin w) :
    Ideal.span (Set.range (orderedOriginal a i j pick ord)) =
      selectedIdeal (TorusCritical.ratio a i j) (TorusCritical.equation a) pick := by
  unfold selectedIdeal incidenceIdeal
  apply congrArg Ideal.span
  exact ord.symm.surjective.range_comp _

theorem orderedOriginal_degree (a : I → Option J → kˣ) (i : I) (j : Option J)
    (pick : Fin r → Equation I J) (ord : Input I J r ≃ Fin w) (t : Fin w) :
    (orderedOriginal a i j pick ord t).totalDegree ≤ 2 :=
  incidenceEquation_quadratic _ _ _ (TorusCritical.ratio_degree a i j)
    (fun s => TorusCritical.equation_degree a (pick s)) (ord.symm t)

theorem combination_degree {q : ℕ} (G : Fin w → MvPolynomial (Fin q) k)
    (deg : ∀t,(G t).totalDegree≤2) (b : ℕ) :
    (StationaryDeformation.combination G b).totalDegree ≤ 2 := by
  apply totalDegree_finsetSum_le
  intro t _
  apply (totalDegree_mul ..).trans
  change ((C (b:k) ^ t.val : MvPolynomial (Fin q) k).totalDegree + (G t).totalDegree) ≤ 2
  rw [←map_pow,totalDegree_C,zero_add]
  exact deg t

end
end PlanarUnitDistances.IntegralGrid
