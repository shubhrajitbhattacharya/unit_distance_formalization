import PlanarUnitDistances.RatioGridDifferential
import PlanarUnitDistances.SmallSideAssembly
import PlanarUnitDistances.MovingGrid

/-! The full original number-field-labeled Euclidean graph obtains a motion
of the fixed-quotient fibre from the published coordinate bound. -/

noncomputable section

namespace PlanarUnitDistances.ResearchMotion

open CartesianGrid TorusCritical Fibre MovingGrid OAI.PlanarUnitDistances


def LocalizedGridWithCap (cap : ℝ → ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [Algebra K ℂ] (I J : Type)
    [Fintype I] [Fintype J] (r : ℕ), StationaryRatioWithCap K ℂ I J r cap


private def cart (p : Plane) : ℂ × ℂ := ((p 0 : ℂ),(p 1 : ℂ))

private theorem cart_inj : Function.Injective cart := by
  intro p q h
  ext j
  fin_cases j
  · exact Complex.ofReal_injective (congrArg Prod.fst h)
  · exact Complex.ofReal_injective (congrArg Prod.snd h)

private theorem chord_cart (p r : Plane) : chordSq (cart p) (cart r) = ((dist p r ^ 2 : ℝ):ℂ) := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp [chordSq,cart,Real.dist_eq,sq_abs]

theorem oriented_with_cap (cap : ℝ → ℝ) (hcap : Monotone cap) (input : LocalizedGridWithCap cap)
    {K I J : Type} [Field K] [NumberField K] (σ : K →+* ℂ) [Fintype I] [Fintype J] [Nontrivial I]
    [Nonempty J] (p : I → ℂ × ℂ) (s : J → ℂ × ℂ) (d : I → J → K) (small : Fintype.card J ≤ 4)
    (same : ∀ i j t, s j=s t → d i j=d i t) (hn : ∀ i j,d i j ≠ 0)
    (hd : ∀ i j, chordSq (p i) (s j)=2-σ (d i j)-(σ (d i j))⁻¹)
    (scale : ℝ) (hscale : 12*(2:ℝ)^111 ≤ scale) (impossible : ∀ h : ℝ, scale/3 ≤ h → h ≤ cap (24*(scale/(324*2^111))) → False)
    (large : ∀ i j, scale/3 ≤ weilHeight (d i j))
    (hr : ∀ i b j t, weilHeight ((d i j*d b t)/(d i t*d b j)) ≤ scale/(324*2^111)) :
    Moving p s (fun i j ↦ σ (d i j)) := by
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  apply small_columns p s _ small (fun i j t h ↦ congrArg σ (same i j t h))
    (fun i j ↦ by simpa only [map_zero] using σ.injective.ne (hn i j)) hd
  intro T _ e hT j j' hj
  let u (i : I) (t : Option T) : Kˣ := Units.mk0 (d i (e t)) (hn i (e t))
  let b : I := Classical.choice inferInstance
  apply velocities_with_cap cap hcap (fun S r => input K S T r) p (s ∘ e) u b hT j j' hj (fun i t ↦ hd i (e t))
    scale hscale impossible (fun i t ↦ large i (e t))
  intro i i' t
  simpa only [labelRectangle,Units.val_div_eq_div_val,Units.val_mul,u,Units.val_mk0] using
    hr i i' (e (some t)) (e none)


private theorem physical_velocities_with_cap (cap : ℝ → ℝ) (hcap : Monotone cap) (input : LocalizedGridWithCap cap) {n : ℕ} {K I J : Type}
    [Field K] [NumberField K] [Fintype I] [Fintype J] [Nontrivial I] [Nontrivial J]
    (G : AdmissibleGraph n K) (impossible : ∀ h : ℝ, G.scale/3 ≤ h → h ≤ cap (24*(G.scale/(324*2^111))) → False) (p : I → Plane) (r : J → Plane)
    (small : Fintype.card I≤4 ∨ Fintype.card J≤4)
    (edges : ∀ i j,(p i,r j)∈G.edges) :
    Moving (cart ∘ p) (cart ∘ r) (fun i j ↦ G.embedding (G.label (p i) (r j))) := by
  let d (i : I) (j : J) := G.label (p i) (r j)
  have cycles (i b j t) := G.rectangle (p i) (p b) (r j) (r t) (edges i j) (edges b t) (edges i t) (edges b j)
  rcases small with h | h
  · apply Moving.transpose (p := cart ∘ r) (s := cart ∘ p) (c := fun j i ↦ G.embedding (d i j))
    refine oriented_with_cap cap hcap input G.embedding _ _ (fun j i ↦ d i j) h
      (fun j i i' he ↦ congrArg (fun v ↦ G.label v (r j)) (cart_inj he))
      (fun j i ↦ G.nonzero _ _ (edges i j)) ?_ G.scale G.scale_bound impossible
      (fun j i ↦ G.large_height _ _ (edges i j)) ?_
    · intro j i
      rw [Function.comp_apply,Function.comp_apply,chord_cart,dist_comm]
      exact G.chord _ _ (edges i j)
    · intro j t i b
      dsimp [d]
      rw [mul_comm (G.label (p b) (r j))]
      exact cycles i b j t
  · refine oriented_with_cap cap hcap input G.embedding _ _ d h
      (fun i j t he ↦ congrArg (G.label (p i)) (cart_inj he))
      (fun i j ↦ G.nonzero _ _ (edges i j)) ?_ G.scale G.scale_bound impossible
      (fun i j ↦ G.large_height _ _ (edges i j)) cycles
    intro i j
    rw [Function.comp_apply,Function.comp_apply,chord_cart]
    exact G.chord _ _ (edges i j)

/-- The original lift includes both the ratios and their inverses over
dual numbers. The chosen constant parameters are precisely their actual
cross ratios, and the first component is the original geometry. -/
theorem motion_with_cap (cap : ℝ → ℝ) (hcap : Monotone cap) (input : LocalizedGridWithCap cap) {n : ℕ} {K : Type}
    [Field K] [NumberField K] (G : AdmissibleGraph n K) (impossible : ∀ h : ℝ, G.scale/3 ≤ h → h ≤ cap (24*(G.scale/(324*2^111))) → False) : MovingGrid.Motion G := by
  intro I J _ _ p r hi hj small edges
  haveI : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  haveI : Nontrivial J := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨H,U,A,b,hm⟩ := physical_velocities_with_cap cap hcap input G impossible p r small edges
  let u (i : I) (j : J) := G.embedding (G.label (p i) (r j))
  let i₀ : I := Classical.choice inferInstance
  let j₀ : J := Classical.choice inferInstance
  let coeff i j := (u i j*u i₀ j₀)/(u i j₀*u i₀ j)
  have hu i j : u i j ≠ 0 := by
    simpa only [u, map_zero] using G.embedding.injective.ne (G.nonzero _ _ (edges i j))
  have hgrid : GridEquations i₀ j₀ (cart ∘ p) (cart ∘ r) u (fun i j ↦ (u i j)⁻¹) coeff := by
    refine ⟨fun i j ↦ (chord_cart _ _).trans (G.chord _ _ (edges i j)),fun i j ↦ mul_inv_cancel₀ (hu i j),?_⟩
    intro i j
    exact (div_mul_cancel₀ _ (mul_ne_zero (hu i j₀) (hu i₀ j))).symm
  refine ⟨⟨i₀,j₀,fun i ↦ liftPosition (cart (p i)) (H i),fun j ↦ liftPosition (cart (r j)) (U j),
    fun i j ↦ liftScalar (u i j) (u i j*(A i-b j)),
    fun i j ↦ liftScalar (u i j)⁻¹ (-(u i j)⁻¹*(A i-b j)),coeff,
    lift_differential i₀ j₀ _ H _ U u _ coeff A b hgrid (fun i j ↦ (hm i j).2),
    fun _ ↦ rfl,fun _ ↦ rfl,fun _ _ ↦ rfl,?_⟩⟩
  exact fun i j ↦ mul_ne_zero (hu i j) (sub_ne_zero.mpr (hm i j).1)


end PlanarUnitDistances.ResearchMotion