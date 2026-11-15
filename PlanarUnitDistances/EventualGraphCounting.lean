import PlanarUnitDistances.Main

namespace PlanarUnitDistances
open OAI.PlanarUnitDistances Filter
open scoped Topology
noncomputable section


theorem AdmissibleGraph.edges_card_le_sq {n : ℕ} {K : Type} [Field K] [NumberField K]
    (G : AdmissibleGraph n K) : G.edges.card ≤ n^2 := by
  have sub : G.edges ⊆ G.points ×ˢ G.points := fun e h => Finset.mem_product.mpr (G.endpoints e h)
  calc
    G.edges.card ≤ (G.points ×ˢ G.points).card := Finset.card_le_card sub
    _ = G.points.card^2 := by rw [Finset.card_product,pow_two]
    _ ≤ n^2 := Nat.pow_le_pow_left G.point_bound 2


end
end PlanarUnitDistances
