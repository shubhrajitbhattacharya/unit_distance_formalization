import PlanarUnitDistances.Heights

/-! A degree-independent height bound for a root of a univariate eliminant.
No integrality or monicity assumption is required. -/

noncomputable section

namespace PlanarUnitDistances.EliminantHeight

open Real Polynomial Height NumberField Height.AdmissibleAbsValues

variable {K : Type*} [Field K]

def coefficients (p : K[X]) (i : Fin (p.natDegree + 1)) : K := p.coeff i

private theorem coeff_le (v : AbsoluteValue K ℝ) (p : K[X]) {i : ℕ} (hi : i ≤ p.natDegree) :
    v (p.coeff i) ≤ ⨆ a, v (coefficients p a) :=
  Finite.le_ciSup_of_le ⟨i, Nat.lt_succ_of_le hi⟩ le_rfl

private theorem root_identity (p : K[X]) {z : K} (hz : p.IsRoot z) :
    p.leadingCoeff * z ^ p.natDegree = -(∑ i ∈ Finset.range p.natDegree, p.coeff i * z^i) := by
  rw [IsRoot.def, eval_eq_sum_range, Finset.sum_range_succ] at hz
  rw [← coeff_natDegree]
  linear_combination hz

/-- Archimedean Cauchy estimate in homogeneous coefficient coordinates. -/
theorem arch_root_bound (v : AbsoluteValue K ℝ) (p : K[X]) (hp : p ≠ 0) {z : K}
    (hz : p.IsRoot z) : v (p.leadingCoeff * z) ≤ 2 * ⨆ j, v (coefficients p j) := by
  let A := ⨆ j, v (coefficients p j)
  let a := v z
  let b := v p.leadingCoeff
  have hb : 0 < b := (v.pos (leadingCoeff_ne_zero.mpr hp))
  have hbA : b ≤ A := coeff_le v p le_rfl
  rw [map_mul]
  change b*a ≤ 2*A
  by_contra! h
  have ha : 1 < a := by
    by_contra! ha
    have hb' := mul_le_mul_of_nonneg_left ha hb.le
    linarith
  have hid := congrArg v (root_identity p hz)
  simp only [map_mul, map_pow, map_neg_eq_map] at hid
  have hineq : b*a^p.natDegree ≤ A*(∑ i ∈ Finset.range p.natDegree, a^i) := by
    rw [Finset.mul_sum]
    calc
      _ = _ := hid
      _ ≤ _ := v.sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun i hi ↦ by
        rw [map_mul, map_pow]
        exact mul_le_mul_of_nonneg_right (coeff_le v p (Finset.mem_range.mp hi).le)
          (pow_nonneg (v.nonneg z) _)
  have hmult := mul_le_mul_of_nonneg_right hineq (sub_nonneg.mpr ha.le)
  rw [mul_assoc A, geom_sum_mul] at hmult
  have hstrong : A < b*a-b := by linarith
  have hbad := mul_lt_mul_of_pos_right hstrong (pow_pos (zero_lt_one.trans ha) p.natDegree)
  nlinarith only [hbad, hmult, hb, hbA]

/-- At nonarchimedean places the leading term is bounded with factor one. -/
theorem nonarch_root_bound (v : AbsoluteValue K ℝ) (hna : IsNonarchimedean v)
    (p : K[X]) (hp : p ≠ 0) {z : K} (hz : p.IsRoot z) :
    v (p.leadingCoeff * z) ≤ ⨆ j, v (coefficients p j) := by
  let A := ⨆ j, v (coefficients p j)
  have hbA : v p.leadingCoeff ≤ A := coeff_le v p le_rfl
  rw [map_mul]
  by_cases ha : v z ≤ 1
  · exact (mul_le_of_le_one_right (v.nonneg _) ha).trans hbA
  have hgt := lt_of_not_ge ha
  have hn : p.natDegree ≠ 0 := by
    intro h
    have hc := eq_C_of_natDegree_eq_zero h
    have hroot := hz
    rw [IsRoot.def, hc, eval_C] at hroot
    have h₀ : p.coeff 0 = 0 := hroot
    exact hp (by simpa [h₀] using hc)
  obtain ⟨d,hd⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hne : (Finset.range p.natDegree).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero hn)⟩
  obtain ⟨i,hi,hle⟩ := hna.finset_image_add_of_nonempty (fun i ↦ p.coeff i * z^i) hne
  have hid := congrArg v (root_identity p hz)
  simp only [map_mul, map_pow, map_neg_eq_map] at hid
  rw [← hid, map_mul, map_pow] at hle
  have hpow : v z ^ i ≤ v z ^ d :=
    pow_le_pow_right₀ hgt.le (by have := Finset.mem_range.mp hi; omega)
  have hbound := hle.trans (mul_le_mul (coeff_le v p (Finset.mem_range.mp hi).le) hpow
    (pow_nonneg (v.nonneg _) _) ((v.nonneg _).trans hbA))
  change v p.leadingCoeff * v z ^ p.natDegree ≤ A * v z ^ d at hbound
  conv at hbound => lhs; rw [hd, pow_succ]
  change v p.leadingCoeff * v z ≤ A
  exact le_of_mul_le_mul_right
    (show (v p.leadingCoeff * v z) * v z ^ d ≤ A * v z ^ d by
      simpa only [mul_assoc, mul_comm (v z) (v z ^ d)] using hbound)
    (pow_pos (zero_lt_one.trans hgt) d)

variable [NumberField K]

def coefficientHeight (p : K[X]) : ℝ := Height.logHeight (coefficients p) / Module.finrank ℚ K

/-- For a root in the coefficient number field (or a common splitting field),
its absolute logarithmic Weil height is bounded by the normalized projective
coefficient height of its defining polynomial plus log 2, in every degree. -/
theorem weilHeight_root_le (p : K[X]) (hp : p ≠ 0) {z : K} (hz : p.IsRoot z) :
    weilHeight z ≤ coefficientHeight p + log 2 := by
  classical
  let x := p.leadingCoeff • (![z, 1] : Fin 2 → K)
  let y := coefficients p
  have hlc := leadingCoeff_ne_zero.mpr hp
  have hx : x ≠ 0 := by
    intro h
    have h' := congrFun h 1
    simp [x, hlc] at h'
  have hy : y ≠ 0 := by
    intro h
    exact hlc (congrFun h (Fin.last p.natDegree))
  have harch (v : AbsoluteValue K ℝ) (i : Fin 2) : v (x i) ≤ 2 * ⨆ j, v (y j) := by
    fin_cases i
    · exact arch_root_bound v p hp hz
    · change v (p.leadingCoeff * 1) ≤ _
      rw [mul_one]
      have hA : v p.leadingCoeff ≤ ⨆ j, v (y j) := coeff_le v p le_rfl
      linarith [v.nonneg p.leadingCoeff]
  have hnon (v : AbsoluteValue K ℝ) (hna : IsNonarchimedean v) (i : Fin 2) :
      v (x i) ≤ ⨆ j, v (y j) := by
    fin_cases i
    · exact nonarch_root_bound v hna p hp hz
    · change v (p.leadingCoeff * 1) ≤ _
      rw [mul_one]
      exact coeff_le v p le_rfl
  have hmul : Height.mulHeight x ≤ (2 : ℝ)^totalWeight K * Height.mulHeight y := by
    rw [Height.mulHeight_eq hx, Height.mulHeight_eq hy]
    have ha : (archAbsVal.map (fun v : AbsoluteValue K ℝ ↦ ⨆ i, v (x i))).prod ≤
        (2 : ℝ)^totalWeight K * (archAbsVal.map (fun v : AbsoluteValue K ℝ ↦ ⨆ j, v (y j))).prod := by
      calc
        _ ≤ (archAbsVal.map (fun v : AbsoluteValue K ℝ ↦ 2 * ⨆ j, v (y j))).prod :=
          Multiset.prod_map_le_prod_map₀ _ _
            (fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _) (fun v _ ↦ ciSup_le (harch v))
        _ = _ := by simp [Multiset.prod_map_mul, totalWeight]
    have hn : (∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i)) ≤ ∏ᶠ v : nonarchAbsVal, ⨆ j, v.val (y j) :=
      finprod_le_finprod₀ (by fun_prop) (fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _)
        (by fun_prop) (fun v ↦ ciSup_le (hnon v.val (isNonarchimedean v.val v.prop)))
    rw [← mul_assoc]
    exact mul_le_mul ha hn (finprod_nonneg fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _)
      (mul_nonneg (by positivity) (Multiset.prod_map_nonneg fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _))
  have hlog := log_le_log (mulHeight_pos _) hmul
  rw [log_mul (by positivity : (2:ℝ)^totalWeight K ≠ 0) (mulHeight_ne_zero y),
    log_pow, NumberField.totalWeight_eq_finrank] at hlog
  change Height.logHeight x ≤ _ + Height.logHeight y at hlog
  rw [show Height.logHeight x = Height.logHeight₁ z from
    (logHeight_smul_eq_logHeight _ hlc).trans (logHeight₁_eq_logHeight z).symm] at hlog
  unfold weilHeight coefficientHeight
  have hD : 0 < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  rw [div_add' _ _ _ hD.ne', div_le_div_iff_of_pos_right hD]
  linarith

end PlanarUnitDistances.EliminantHeight
