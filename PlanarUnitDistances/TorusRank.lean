import PlanarUnitDistances.TorusCritical

/-! Rigid motions on the explicit grid torus and the Jacobian rank loss. -/

noncomputable section

namespace PlanarUnitDistances.TorusCritical

open MvPolynomial CriticalLocus

section Differential

variable {X k : Type*} [Fintype X] [Field k] (x v : X → k)

theorem derivative_constant (c : k) : jacobianRow x (C c) v = 0 := by
  simp [jacobianRow]

theorem derivative_variable (i : X) : jacobianRow x (MvPolynomial.X i : MvPolynomial X k) v = v i := by
  classical
  simp [jacobianRow, pderiv_X, Pi.single_apply, apply_ite]

theorem derivative_add (f g : MvPolynomial X k) :
    jacobianRow x (f + g) v = jacobianRow x f v + jacobianRow x g v := by
  simp [jacobianRow, LinearMap.sum_apply, add_mul, Finset.sum_add_distrib]

theorem derivative_sub (f g : MvPolynomial X k) :
    jacobianRow x (f - g) v = jacobianRow x f v - jacobianRow x g v := by
  simp [jacobianRow, LinearMap.sum_apply, sub_mul, Finset.sum_sub_distrib]

theorem derivative_mul (f g : MvPolynomial X k) :
    jacobianRow x (f * g) v = jacobianRow x f v * eval x g + eval x f * jacobianRow x g v := by
  simp only [jacobianRow, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, pderiv_mul,
    map_add, map_mul, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, aeval_eq_eval]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

end Differential

variable {I J k : Type*} [Field k] (p : I → k × k) (s : Option J → k × k)

/-- Two translations and one rotation, with all unit coordinates fixed. -/
def rigidVelocity (w : Fin 3 → k) : Coord I J → k
  | .inl (i,h) => ![w 0 - w 2 * (p i).2, w 1 + w 2 * (p i).1, 0, 0] h
  | .inr (.inl (j,h)) => ![w 0 - w 2 * (s j).2, w 1 + w 2 * (s j).1] h
  | .inr (.inr _) => 0

def rigidMap : (Fin 3 → k) →ₗ[k] (Coord I J → k) where
  toFun := rigidVelocity p s
  map_add' u v := by
    funext c
    rcases c with ⟨i,h⟩ | (⟨j,h⟩ | j)
    · fin_cases h <;> simp [rigidVelocity] <;> ring
    · fin_cases h <;> simp [rigidVelocity] <;> ring
    · simp [rigidVelocity]
  map_smul' b v := by
    funext c
    rcases c with ⟨i,h⟩ | (⟨j,h⟩ | j)
    · fin_cases h <;> simp [rigidVelocity] <;> ring
    · fin_cases h <;> simp [rigidVelocity] <;> ring
    · simp [rigidVelocity]

theorem rigidMap_injective (j j' : Option J) (h : s j ≠ s j') :
    Function.Injective (rigidMap p s) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro w hw
  have h₁ (j : Option J) : w 0 - w 2 * (s j).2 = 0 :=
    congrFun hw (.inr (.inl (j,0)))
  have h₂ (j : Option J) : w 1 + w 2 * (s j).1 = 0 :=
    congrFun hw (.inr (.inl (j,1)))
  have hw₂ : w 2 = 0 := by
    by_contra hne
    apply h
    apply Prod.ext
    · apply mul_left_cancel₀ hne
      linear_combination h₂ j - h₂ j'
    · apply mul_left_cancel₀ hne
      linear_combination h₁ j' - h₁ j
  have hw₀ := h₁ j
  have hw₁ := h₂ j
  simp only [hw₂, zero_mul, sub_zero, add_zero] at hw₀ hw₁
  funext i
  fin_cases i <;> assumption

variable [Fintype I] [Fintype J] (a : I → Option J → kˣ) (i₀ : I)
  (sol : Fibre.TorusSolution i₀ none p s a)

theorem equation_annihilates_rigid (e : Equation I J) (w : Fin 3 → k) :
    jacobianRow (coordinates p s a i₀ sol) (equation a e) (rigidMap p s w) = 0 := by
  change jacobianRow _ _ (rigidVelocity p s w) = 0
  have hu (j : Option J) (h : Fin 2) :
      jacobianRow (coordinates p s a i₀ sol) (colUnit (k := k) j h) (rigidVelocity p s w) = 0 := by
    cases j with
    | none => exact derivative_constant _ _ 1
    | some j => exact derivative_variable _ _ _
  have hone : jacobianRow (coordinates p s a i₀ sol) (1 : Poly I J k) (rigidVelocity p s w) = 0 :=
    derivative_constant _ _ 1
  rcases e with i | (j | ⟨i,j⟩)
  · simp [equation, derivative_sub, derivative_mul, derivative_variable, hone, rigidVelocity]
  · simp [equation, derivative_sub, derivative_mul, hu, hone]
  · simp [equation, ratio, inverseRatio, positionDifference, pow_two, derivative_add,
      derivative_sub, derivative_mul, derivative_variable, derivative_constant, hu, rigidVelocity, coordinates]
    ring

/-- The two distinct anchor positions make three independent velocities lie in
the Jacobian kernel, even if the grid point is singular. -/
theorem torus_jacobian_rank_bound (j j' : Option J) (h : s j ≠ s j') :
    Module.finrank k (Submodule.span k (Set.range
      (fun e ↦ jacobianRow (coordinates p s a i₀ sol) (equation a e)))) + 3 ≤
        4 * (Fintype.card I + Fintype.card (Option J)) - 2 := by
  let M := LinearMap.range (rigidMap p s)
  have hm : Module.finrank k M = 3 := by
    rw [show M = LinearMap.range (rigidMap p s) from rfl,
      LinearMap.finrank_range_of_inj (rigidMap_injective p s j j' h), Module.finrank_pi]
    simp
  have hle : Submodule.span k (Set.range
      (fun e ↦ jacobianRow (coordinates p s a i₀ sol) (equation a e))) ≤ M.dualAnnihilator := by
    apply Submodule.span_le.mpr
    rintro _ ⟨e,rfl⟩
    apply (Submodule.mem_dualAnnihilator _).mpr
    rintro _ ⟨w,rfl⟩
    exact equation_annihilates_rigid p s a i₀ sol e w
  calc
    _ ≤ Module.finrank k M.dualAnnihilator + 3 := Nat.add_le_add_right (Submodule.finrank_mono hle) _
    _ = Fintype.card (Coord I J) := by
      have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq M
      rw [hm, Module.finrank_pi] at hd
      exact (add_comm _ _).trans hd
    _ = _ := by simp [Coord]; omega

end PlanarUnitDistances.TorusCritical
