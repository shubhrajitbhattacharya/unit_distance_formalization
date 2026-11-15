import PlanarUnitDistances.EmpiricalCross
import PlanarUnitDistances.ListComparisons
import PlanarUnitDistances.PosteriorCut

namespace OAI.PlanarUnitDistances.CommonTemplate
open Finset FiniteLaw FiniteStarCoupling CrossSampling CrossStructure StrictCross
open scoped Classical
noncomputable section
variable {P Q A B H I : Type*} [Fintype P] [Fintype Q] [Fintype A] [Fintype B]
  [Fintype H] [Fintype I] [Nonempty I]

def historyLaw (π : Law (P×Q)) (h : P → H) (q : Q) := push (col π q) h

def listLaw (π : Law (P×Q)) (h : P → H) (q : Q) := independent (historyLaw π h q) I

def candidates (ν : H → Law (A×B)) (ζ : ℝ) (θ : I → H) : Finset (A×B) :=
  univ.filter fun y => 1-ζ ≤ (∑ i, crossMass (ν (θ i)) y)/(Fintype.card I:ℝ)

def accurate (μ : Law H) (ν : H → Law (A×B)) (u : ℝ) (θ : I → H) :=
  ∀ y : A×B, |empiricalError μ (fun a => crossMass (ν a) y) θ| ≤ u

omit [Nonempty I] in
lemma candidate_mass (μ : Law H) (ν : H → Law (A×B)) (θ : I → H) {ζ u : ℝ}
    (ha : accurate μ ν u θ) {y : A×B} (hy : y ∈ candidates ν ζ θ) :
    1-(ζ+u) ≤ crossMass (mix μ ν) y := by
  have h := (abs_le.mp (ha y)).2
  have b := (mem_filter.mp hy).2
  change 1-ζ ≤ _ at b
  unfold empiricalError at h
  change _ ≤ avg (mix μ ν) _
  rw [mix_avg]
  change _ ≤ avg μ (fun a => crossMass (ν a) y)
  linarith

theorem empirical_list_failure (μ : Law H) (ν : H → Law (A×B)) (u : ℝ) (hu : 0 < u) :
    event (independent μ I) (fun θ => ¬accurate μ ν u θ) ≤ 16/((Fintype.card I:ℝ)*u^2) := by
  exact (event_congr _ (fun _ => by simp [accurate])).trans_le (empirical_cross_tail μ ν hu)

theorem omitted_center (μ : Law H) (ν : H → Law (A×B)) (y : A×B) {ζ : ℝ} (hζ : 0 < ζ) :
    event (independent μ I) (fun θ => y ∉ candidates ν ζ θ) ≤
      (1 - avg μ (fun a => crossMass (ν a) y))/ζ := by
  let f (θ : I → H) := (∑ i, crossMass (ν (θ i)) y)/(Fintype.card I:ℝ)
  have le1 (θ : I → H) : f θ ≤ 1 := by
    apply (div_le_one (Nat.cast_pos.mpr Fintype.card_pos)).mpr
    calc
      _ ≤ ∑ _i : I, (1:ℝ) := sum_le_sum fun i _ => event_le_one (ν (θ i)) _
      _ = _ := by simp
  have eqv : avg (independent μ I) f = avg μ (fun a => crossMass (ν a) y) := by
    dsimp [f]
    have hv (i : I) := independent_single μ i (fun a => crossMass (ν a) y)
    simp only [div_eq_inv_mul,avg_smul,avg_sum,hv,Finset.sum_const,card_univ,nsmul_eq_mul,← mul_assoc]
    rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero : (Fintype.card I:ℝ) ≠ 0),one_mul]
  have h := event_markov (independent μ I) (fun θ => 1-f θ) (fun θ => sub_nonneg.mpr (le1 θ)) hζ
  rw [avg_sub,avg_const,eqv] at h
  apply (event_mono _ (fun θ (hbad : y ∉ candidates ν ζ θ) => ?_)).trans h
  have hb : ¬1-ζ ≤ f θ := fun h => hbad (mem_filter.mpr ⟨mem_univ _,h⟩)
  linarith

private lemma witness_mass (π : Law (A×B)) (W U : Finset (A×B)) {b : ℝ} (hb : 0 ≤ b)
    (hc : W.card ≤ 3) (hin : ∀ x, (∀ y ∈ W, Adj x y) → x ∈ U)
    (hh : ∀ y ∈ W, 1-b ≤ crossMass π y) : 1-3*b ≤ event π (fun x => x ∈ U) := by
  have each (x : A×B) : (if x ∉ U then (1:ℝ) else 0) ≤
      ∑ y ∈ W, if ¬Adj x y then (1:ℝ) else 0 := by
    by_cases hx : x ∈ U
    · simp [hx]; positivity
    have ex : ∃ y ∈ W, ¬Adj x y := by by_contra! no; exact hx (hin x no)
    obtain ⟨z,hz,hn⟩ := ex
    simp only [hx, not_false_eq_true, if_true]
    exact (show (1:ℝ) = (if ¬Adj x z then 1 else 0) by simp [hn]).trans_le
      (single_le_sum (s := W) (f := fun y => if ¬Adj x y then (1:ℝ) else 0) (fun y _ => by split <;> norm_num) hz)
  have bd := avg_mono π each
  rw [avg_ite,event_compl] at bd
  have sum : avg π (fun x => ∑ y ∈ W, if ¬Adj x y then (1:ℝ) else 0) =
      ∑ y ∈ W, event π (fun x => ¬Adj x y) := by
    unfold avg event
    simp only [avg,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : Adj x y <;> simp [h]
  rw [sum] at bd
  have cap : (∑ y ∈ W, event π (fun x => ¬Adj x y)) ≤ (W.card:ℝ)*b := calc
    _ ≤ ∑ _y ∈ W, b := sum_le_sum fun y hy => by
      rw [event_compl]; change 1 - crossMass π y ≤ b; linarith [hh y hy]
    _ = _ := by simp
  have cr : (W.card:ℝ) ≤ 3 := by exact_mod_cast hc
  exact (sub_le_comm.mp (by
    exact bd.trans (cap.trans (mul_le_mul_of_nonneg_right cr hb))))

omit [Nonempty I] in
theorem list_choice (ν : H → Law (A×B)) {ζ u : ℝ} (hζ : 0 ≤ ζ) (hu : 0 ≤ u) (θ : I → H) :
    ∃ U : Finset (A×B), (U=univ ∨ RestrictedTransfer.Permitted U) ∧
      Shape (candidates ν ζ θ) U ∧
      ∀ μ : Law H, accurate μ ν u θ → 1-3*(ζ+u) ≤ event (mix μ ν) (fun x => x∈U) := by
  obtain ⟨W,U,sub,hc,perm,inter,shape⟩ := witnesses (candidates ν ζ θ)
  exact ⟨U,perm,shape,fun μ h =>
    witness_mass (mix μ ν) W U (add_nonneg hζ hu) hc inter
      (fun y hy => candidate_mass μ ν θ h (sub hy))⟩

end
end OAI.PlanarUnitDistances.CommonTemplate
