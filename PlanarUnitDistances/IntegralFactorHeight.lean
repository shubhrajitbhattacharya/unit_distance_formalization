import PlanarUnitDistances.IntegerInterpolation

namespace PlanarUnitDistances.IntegralFactorHeight

open MvPolynomial
noncomputable section

private theorem eval_univariate_slice {n : ℕ} (f : MvPolynomial (Fin (n+1)) ℤ)
    (u : Fin n → ℤ) (x : ℤ) :
    (((finSuccEquiv ℤ n f).map (eval u)).eval x) = eval (Fin.cases x u) f := by
  have e := Polynomial.eval_map_apply (p := finSuccEquiv ℤ n f) (eval u) (C x)
  simpa only [eval_C, eval_polynomial_eval_finSuccEquiv] using e

private theorem coeff_slice_degree {n : ℕ} (f : MvPolynomial (Fin (n+1)) ℤ) (k : ℕ) :
    ((finSuccEquiv ℤ n f).coeff k).totalDegree ≤ f.totalDegree := by
  by_cases h : (finSuccEquiv ℤ n f).coeff k = 0
  · simp [h]
  · have := totalDegree_coeff_finSuccEquiv_add_le f k h
    omega

/-- Integer interpolation on a finite box after removing the zero locus of a nonzero
    polynomial. Both degrees may equal zero. -/
theorem coeff_le_away_from_hypersurface (n D M B : ℕ) (S : Finset ℤ)
    (hcard : 2 * D < S.card) (hsize : ∀ x ∈ S, Int.natAbs x ≤ M)
    (f h : MvPolynomial (Fin n) ℤ) (hf : f.totalDegree ≤ D)
    (hh : h.totalDegree ≤ D) (hne : h ≠ 0)
    (hval : ∀ u : Fin n → ℤ, (∀ i, u i ∈ S) → eval u h ≠ 0 → (eval u f).natAbs ≤ B)
    (a : Fin n →₀ ℕ) :
    (f.coeff a).natAbs ≤ B * ((2 * (M + 2)) ^ D) ^ n := by
  classical
  induction n generalizing B with
  | zero =>
    let u : Fin 0 → ℤ := Fin.elim0
    obtain ⟨b, rfl⟩ := (isEmptyAlgEquiv ℤ (Fin 0)).symm.surjective f
    obtain ⟨c, rfl⟩ := (isEmptyAlgEquiv ℤ (Fin 0)).symm.surjective h
    simp only [isEmptyAlgEquiv_symm_apply] at *
    have hc : c ≠ 0 := by intro hc; simp [hc] at hne
    have hv := hval u (fun i => Fin.elim0 i) (by simpa using hc)
    have ha : a = 0 := Subsingleton.elim _ _
    rw [ha, coeff_C]
    simpa using hv
  | succ n ih =>
    have hhn : finSuccEquiv ℤ n h ≠ 0 := by simpa using hne
    obtain ⟨j, hj⟩ : ∃ j, (finSuccEquiv ℤ n h).coeff j ≠ 0 := by
      by_contra! hn
      exact hhn (Polynomial.ext (by simpa using hn))
    let k := a 0
    let fk := (finSuccEquiv ℤ n f).coeff k
    let hjp := (finSuccEquiv ℤ n h).coeff j
    have step (u : Fin n → ℤ) (hu : ∀ i, u i ∈ S) (huj : eval u hjp ≠ 0) :
        (eval u fk).natAbs ≤ B * (2 * (M+2)) ^ D := by
      let P := (finSuccEquiv ℤ n f).map (eval u)
      let H := (finSuccEquiv ℤ n h).map (eval u)
      have hn : H ≠ 0 := by
        intro hh0
        have e := congrArg (fun z : Polynomial ℤ => z.coeff j) hh0
        exact huj (by simpa only [H, Polynomial.coeff_map, Polynomial.coeff_zero] using e)
      have dP : P.natDegree ≤ D := by
        exact (Polynomial.natDegree_map_le ..).trans
          ((natDegree_finSuccEquiv f ▸ degreeOf_le_totalDegree f 0).trans hf)
      have dH : H.natDegree ≤ D := by
        exact (Polynomial.natDegree_map_le ..).trans
          ((natDegree_finSuccEquiv h ▸ degreeOf_le_totalDegree h 0).trans hh)
      let good := S \ H.roots.toFinset
      have hroots : H.roots.toFinset.card ≤ D :=
        (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' H).trans dH)
      have enough : D < good.card := by
        have := Finset.le_card_sdiff H.roots.toFinset S
        dsimp [good]
        omega
      have hb := coeff_le_of_integer_nodes D P good M B dP enough
        (fun _ hx => hsize _ (Finset.mem_sdiff.mp hx).1) (by
          intro x hx
          obtain ⟨hxS,hxr⟩ := Finset.mem_sdiff.mp hx
          have hxH : H.eval x ≠ 0 := by
            simpa only [Multiset.mem_toFinset, Polynomial.mem_roots hn, Polynomial.IsRoot] using hxr
          rw [show P.eval x = _ from eval_univariate_slice f u x]
          apply hval
          · exact Fin.cases hxS hu
          · simpa only [← eval_univariate_slice h u x] using hxH) k
      simpa only [P, fk, Polynomial.coeff_map] using hb
    have bound := ih (B * (2 * (M+2)) ^ D) fk hjp
      ((coeff_slice_degree f k).trans hf) ((coeff_slice_degree h j).trans hh) hj step a.tail
    simpa only [fk, k, finSuccEquiv_coeff_coeff, Finsupp.cons_tail, pow_succ,
      mul_assoc, mul_left_comm, mul_comm] using bound

/-- On the integer box a nonzero value of the cofactor has absolute value at least one.
    This transfers a bound on the values of a multiple to the coefficients of any divisor. -/
theorem coeff_factor_le_of_box (n D B : ℕ) (g f : MvPolynomial (Fin n) ℤ)
    (hdiv : f ∣ g) (hg : g ≠ 0) (hdeg : g.totalDegree ≤ D)
    (hbox : ∀ u : Fin n → ℤ, (∀ i, 0 ≤ u i ∧ u i ≤ (2*D : ℕ)) → (eval u g).natAbs ≤ B)
    (a : Fin n →₀ ℕ) :
    (f.coeff a).natAbs ≤ B * ((2 * (2*D + 2)) ^ D) ^ n := by
  classical
  obtain ⟨h, he⟩ := hdiv
  let S := Finset.Icc (0 : ℤ) (2*D : ℕ)
  have hs : 2*D < S.card := by
    dsimp [S]
    rw [Int.card_Icc]
    omega
  refine coeff_le_away_from_hypersurface n D (2*D) B S hs ?_ f h
    ((totalDegree_le_of_dvd_of_isDomain ⟨h, he⟩ hg).trans hdeg)
    ((totalDegree_le_of_dvd_of_isDomain ⟨f, he.trans (mul_comm f h)⟩ hg).trans hdeg)
    (by intro hz; simp [he, hz] at hg) ?_ a
  · intro x hx
    obtain ⟨h0, htop⟩ := Finset.mem_Icc.mp hx
    exact_mod_cast (Int.natAbs_of_nonneg h0 ▸ htop : (x.natAbs : ℤ) ≤ (2*D : ℕ))
  · intro u hu hnu
    have hb := hbox u (fun i => Finset.mem_Icc.mp (hu i))
    rw [he, map_mul, Int.natAbs_mul] at hb
    exact (Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr hnu)).trans hb

/-- The possible monomial exponent vectors lie in a product of closed degree intervals. -/
theorem support_card_bound {σ : Type*} [Fintype σ] (f : MvPolynomial σ ℤ)
    (D : ℕ) (hd : f.totalDegree ≤ D) : f.support.card ≤ (D+1) ^ Fintype.card σ := by
  classical
  let e (a : f.support) (i : σ) : Fin (D+1) :=
    ⟨a.val i, Nat.lt_succ_of_le ((le_degreeOf_of_mem_support i a.property).trans
      ((degreeOf_le_totalDegree f i).trans hd))⟩
  have h : Function.Injective e := by
    intro a b h
    exact Subtype.ext (Finsupp.ext fun i => congrArg Fin.val (congrFun h i))
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using
    Fintype.card_le_of_injective e h


/-- Version for an arbitrary finite coefficient parameter type. -/
theorem factor_sum_le {σ : Type*} [Fintype σ] (D B : ℕ) (g f : MvPolynomial σ ℤ)
    (hdiv : f ∣ g) (hg : g ≠ 0) (hdeg : g.totalDegree ≤ D)
    (hbox : ∀ u : σ → ℤ, (∀ i, 0 ≤ u i ∧ u i ≤ (2*D : ℕ)) → (eval u g).natAbs ≤ B) :
    (∑ a ∈ f.support, (f.coeff a).natAbs) ≤
      (D+1)^(Fintype.card σ) * (B * ((2 * (2*D + 2)) ^ D) ^ Fintype.card σ) := by
  classical
  let e := Fintype.equivFin σ
  let E := renameEquiv ℤ e
  have hg' : E g ≠ 0 := by simpa using hg
  have hd' : (E g).totalDegree ≤ D := (totalDegree_renameEquiv e g).le.trans hdeg
  have hb' (u : Fin (Fintype.card σ) → ℤ)
      (hu : ∀ i, 0 ≤ u i ∧ u i ≤ (2*D : ℕ)) : (eval u (E g)).natAbs ≤ B := by
    change (eval u (rename e g)).natAbs ≤ B
    rw [eval_rename]
    exact hbox _ (fun i => hu (e i))
  have each a : (f.coeff a).natAbs ≤ B * ((2 * (2*D + 2)) ^ D) ^ Fintype.card σ := by
    have hb := coeff_factor_le_of_box _ D B (E g) (E f) (map_dvd E hdiv) hg' hd' hb'
      (Finsupp.mapDomain e a)
    change ((rename e f).coeff (Finsupp.mapDomain e a)).natAbs ≤ _ at hb
    rwa [coeff_rename_mapDomain e e.injective] at hb
  calc
    _ ≤ ∑ _a ∈ f.support, (B * ((2 * (2*D + 2)) ^ D) ^ Fintype.card σ) :=
      Finset.sum_le_sum fun a _ => each a
    _ ≤ _ := by
      simpa only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id] using Nat.mul_le_mul_right _
        (support_card_bound f D ((totalDegree_le_of_dvd_of_isDomain hdiv hg).trans hdeg))

end
end PlanarUnitDistances.IntegralFactorHeight
