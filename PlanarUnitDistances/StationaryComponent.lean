import PlanarUnitDistances.SparseTorus
import PlanarUnitDistances.Stationarity

/-! The reduced stationary grid and its constant-output irreducible component
with the exact budgets used for arithmetic intersection. -/

noncomputable section

namespace PlanarUnitDistances.TorusCritical

open CriticalLocus MvPolynomial

variable {I J k : Type*} [Field k] [CharZero k] [IsAlgClosed k] [Fintype I] [Fintype J]

/-- The component of the selected grid is defined in at most 98 variables by
quadrics. Its value is the chord ratio of the *original* target edge. -/
theorem sparse_stationary_component [Nontrivial I] (p : I → k × k) (s : Option J → k × k)
    (a : I → Option J → kˣ) (i₀ : I) (sol : Fibre.TorusSolution i₀ none p s a)
    (ha : ∀ i, a i none = 1) (hl : Fintype.card (Option J) ≤ 4)
    (iₑ : I) (jₑ j j' : Option J) (hj : s j ≠ s j')
    (hs : ∀ v : Coord I J → k, (∀ e, jacobianRow (coordinates p s a i₀ sol) (equation a e) v = 0) →
      jacobianRow (coordinates p s a i₀ sol) (ratio a iₑ jₑ) v = 0) :
    ∃ (S : Finset I) (hi : iₑ ∈ S), 2 ≤ S.card ∧ S.card ≤ 3 * Fintype.card (Option J) - 3 ∧
      (S.card - 1) * (Fintype.card (Option J) - 1) ≤ 24 ∧
      ∀ b₀ : S, let β := restrictedCoefficient a S b₀
        let x := coordinates (fun i : S ↦ p i) s β b₀ (restrictedSolution p s a i₀ sol S b₀ ha)
        ∃ (r : ℕ) (pick : Fin r → Equation S J) (t : Fin r → k),
          r ≤ 47 ∧ Fintype.card (Variables (Coord S J) (Fin r)) ≤ 98 ∧
          ∃ P ∈ (incidenceIdeal (ratio β ⟨iₑ,hi⟩ jₑ) (equation β) pick).minimalPrimes,
            P ≤ RingHom.ker (aeval (liftedPoint x t (chordRatio p s a i₀ sol iₑ jₑ))) ∧
            outputVariable - C (chordRatio p s a i₀ sol iₑ jₑ) ∈ P ∧
            ∀ e, (incidenceEquation (ratio β ⟨iₑ,hi⟩ jₑ) (equation β) pick e).totalDegree ≤ 2 := by
  classical
  obtain ⟨S, hi, h₂, hmax, hsub⟩ := sparse_subgrid p s a i₀ sol ha iₑ jₑ j j' hj hs
  have hl₂ : 2 ≤ Fintype.card (Option J) :=
    Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨j,j',fun h ↦ hj (congrArg s h)⟩⟩
  have hm := small_grid_sizes (m := S.card) (r := 0) hl₂ hl hmax (Nat.zero_le _)
  refine ⟨S, hi, h₂, hmax, hm.2.1, ?_⟩
  intro b₀
  let β := restrictedCoefficient a S b₀
  let p' := fun i : S ↦ p i
  let sol' := restrictedSolution p s a i₀ sol S b₀ ha
  let ie' : S := ⟨iₑ,hi⟩
  dsimp only
  obtain ⟨r,pick,t,hr,_hlin,P,hmin,hlift,hval,hdeg⟩ :=
    stationary_ratio_component p' s β b₀ sol' ie' jₑ (hsub b₀)
  have hrank := torus_jacobian_rank_bound p' s β b₀ sol' j j' hj
  rw [← hr, Fintype.card_coe] at hrank
  have hbud := small_grid_sizes (m := S.card) (r := r) hl₂ hl hmax (by omega)
  have hcoord : Fintype.card (Variables (Coord S J) (Fin r)) =
      (4*(S.card+Fintype.card (Option J))-2)+r+1 := by
    simp [Variables, Coord]
    omega
  have hc : (↑(β ie' jₑ * sol'.row ie' * sol'.col jₑ) : k) = chordRatio p s a i₀ sol iₑ jₑ :=
    restricted_chordRatio p s a i₀ sol S b₀ ha ie' jₑ
  rw [hc] at hlift hval
  exact ⟨r,pick,t,by omega, hcoord.trans_le hbud.2.2,P,hmin,hlift,hval,hdeg⟩

end PlanarUnitDistances.TorusCritical
