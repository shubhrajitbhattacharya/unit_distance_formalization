import PlanarUnitDistances.IntegralGridEquations

namespace PlanarUnitDistances.IntegralGrid
open MvPolynomial CriticalLocus EliminantHeight
open TorusCritical (Coord Equation RatioParameters)
noncomputable section
variable {I J : Type*} {r : ℕ}

abbrev Input (I J : Type*) (r : ℕ) := (Fin r) ⊕ (Coord I J ⊕ Unit)
abbrev Slots (I J : Type*) (r : ℕ) := Variables (Coord I J) (Fin r)

/-- Integer selected multiplier system: exactly the r primal rows, the
coordinate-gradient rows, and the constant-output row. -/
def table (i : I) (j : Option J) (pick : Fin r → Equation I J) :
    Input I J r → InStates (RatioParameters I J) (Slots I J r)
  | .inl a => rename Sum.inl (equation (pick a))
  | .inr (.inl x) => rename Sum.inl (pderiv x (ratio i j)) -
      ∑ a, X (.inr (.inl a)) * rename Sum.inl (pderiv x (equation (pick a)))
  | .inr (.inr ()) => X (.inr (.inr ())) - rename Sum.inl (ratio i j)

theorem map_table {k : Type*} [Field k] (a : I → Option J → kˣ) (i : I) (j : Option J)
    (pick : Fin r → Equation I J) (e : Input I J r) :
    MvPolynomial.map (atLabels a) (table i j pick e) =
      incidenceEquation (TorusCritical.ratio a i j) ((TorusCritical.equation a) ∘ pick) id e := by
  rcases e with e | (x | ⟨⟩) <;>
    simp [table,incidenceEquation,outputVariable,map_rename,←pderiv_map,map_equation,map_ratio]

theorem table_bound (i : I) (j : Option J) (pick : Fin r → Equation I J) (hr : r ≤ 47) (e : Input I J r) :
    Bound 1130 (table i j pick e) := by
  have hq := ratio_bound i j
  rcases e with h | (x | ⟨⟩)
  · exact ((equation_bound (pick h)).rename _ Sum.inl_injective).mono (by decide)
  · have part (a : Fin r) : Bound 24
        (X (.inr (.inl a) : Slots I J r)*rename Sum.inl (pderiv x (equation (pick a)))) := by
      rw [mul_comm]
      exact (((equation_bound _).pderiv (equation_degree _) x).rename _ Sum.inl_injective).mul_X _
    have tot := Bound.sum Finset.univ _ part
    simp only [Finset.card_univ,Fintype.card_fin] at tot
    exact ((((hq.pderiv (ratio_degree i j) x).rename _ Sum.inl_injective).sub tot)).mono (by omega)
  · exact ((Bound.X _).sub (hq.rename _ Sum.inl_injective)).mono (by decide)

private theorem partial_degree {A X : Type*} [CommRing A] {p : MvPolynomial X A} {d : ℕ} (i : X)
    (hp : p.totalDegree ≤ d+1) : (pderiv i p).totalDegree ≤ d := by
  classical
  apply Finset.sup_le
  intro m hm
  have hn := mem_support_iff.mp hm
  rw [coeff_pderiv] at hn
  have hs : m + Finsupp.single i 1 ∈ p.support := mem_support_iff.mpr (left_ne_zero_of_mul hn)
  have hd := (le_totalDegree hs).trans hp
  simpa [Finsupp.sum_add_index'] using hd

theorem table_state_degree (i : I) (j : Option J) (pick : Fin r → Equation I J) (e : Input I J r) :
    (table i j pick e).totalDegree ≤ 2 := by
  classical
  rcases e with a | (x | ⟨⟩)
  · exact (totalDegree_rename_le _ _).trans (equation_degree (pick a))
  · apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (totalDegree_rename_le _ _).trans ((partial_degree x (ratio_degree i j)).trans (by decide))
    · apply totalDegree_finsetSum_le
      intro t _
      apply (totalDegree_mul _ _).trans
      rw [totalDegree_X]
      have ht := (totalDegree_rename_le (Sum.inl : Coord I J → Slots I J r) _).trans
        (partial_degree (d:=1) x (equation_degree (pick t)))
      omega
  · apply (totalDegree_sub _ _).trans
    exact max_le (by simp) ((totalDegree_rename_le _ _).trans (ratio_degree i j))

end
end PlanarUnitDistances.IntegralGrid
