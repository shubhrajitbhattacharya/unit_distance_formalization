import PlanarUnitDistances.BinaryDiagonal
import PlanarUnitDistances.CrossComparisons

namespace OAI.PlanarUnitDistances.BinaryMinority
open Finset FiniteLaw FiniteStarCoupling StarScore
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

private def majority {T : Type*} [Fintype T] (μ : Law T) (b : T → Bool) :=
  decide (1/2 ≤ frequency μ b)

private theorem wrong_majority {T : Type*} [Fintype T] (μ : Law T) (b : T → Bool) :
    event μ (fun t => b t≠majority μ b) ≤ variation μ b := by
  let r := frequency μ b
  have lo : 0≤r := frequency_nonneg _ _
  have hi : r≤1 := frequency_le_one _ _
  change _ ≤ 2*r*(1-r)
  by_cases h : 1/2≤r
  · have hm : majority μ b=true := decide_eq_true h
    rw [hm,event_compl]
    change 1-r ≤ _
    nlinarith [mul_nonneg (show 0≤2*r-1 by linarith) (sub_nonneg.mpr hi)]
  · have hm : majority μ b=false := decide_eq_false h
    rw [hm, event_congr μ (P:=fun t => b t≠false) (Q:=fun t => b t=true)
      (fun t => by cases b t <;> simp)]
    change r ≤ _
    nlinarith [mul_nonneg lo (show 0≤1-2*r by linarith)]

private theorem bool_total {T : Type*} [Fintype T] (μ : Law T) (i : T → Bool) (b : Bool) :
    event μ (fun t => i t=b)+event μ (fun t => i t=(!b))=1 := by
  have he := event_compl μ (fun t => i t=b)
  rw [event_congr μ (P:=fun t => ¬i t=b) (Q:=fun t => i t=(!b))
    (fun t => by cases b <;> cases i t <;> decide)] at he
  linarith

/-- Expansion and the two lower marginals select a binary label whose
equal-label rectangle has edge mass at most nine times the mismatch. -/
theorem lighter_label (π : Law (P×Q)) {ξ : ℝ} (U : Law P) (V : Law Q)
    (rect : ∀ (A : P → Prop) (B : Q → Prop), event π (fun e => A e.1 ∧ B e.2) ≤
      let z := Real.sqrt (event U A*event V B)
      z*(z^(2/25:ℝ)+ξ))
    (lowP : ∀ A : P → Prop, (27/50:ℝ)*event U A≤event π (fun e => A e.1))
    (lowQ : ∀ B : Q → Prop, (27/50:ℝ)*event V B≤event π (fun e => B e.2))
    (hξ : 0≤ξ) (hs : ξ≤1/(2:ℝ)^100) (x : P → Bool) (y : Q → Bool) :
    ∃ b : Bool, event π (fun e => x e.1=b ∧ y e.2=b) ≤
      9*event π (fun e => x e.1≠y e.2) := by
  let u (b : Bool) := event U (fun p => x p=b)
  let v (b : Bool) := event V (fun q => y q=b)
  let z (b : Bool) := Real.sqrt (u b*v b)
  let d (b : Bool) := event π (fun e => x e.1=b ∧ y e.2=b)
  let s := event π (fun e => x e.1≠y e.2)
  obtain ⟨b,hb⟩ : ∃ b : Bool, z b≤z (!b) := by
    by_cases h : z true≤z false
    · exact ⟨true,h⟩
    · exact ⟨false,le_of_not_ge h⟩
  refine ⟨b,?_⟩
  have uT : u b+u (!b)=1 := bool_total U x b
  have vT : v b+v (!b)=1 := bool_total V y b
  have un (a) : 0≤u a := event_nonneg _ _
  have vn (a) : 0≤v a := event_nonneg _ _
  have identity (F G : (P×Q) → Prop) (c : ℝ) :
      event π F+c*event π G=avg π (fun e => (if F e then 1 else 0)+c*(if G e then 1 else 0)) := by
    rw [avg_add,avg_smul,avg_ite,avg_ite]
  have dsum : d b+d (!b)=1-s := by
    change event π _+event π _=1-event π _
    rw [←event_compl]
    unfold event
    rw [←avg_add]
    apply avg_congr
    intro e
    cases b <;> cases hx : x e.1 <;> cases hy : y e.2 <;> norm_num [hx,hy]
  have both : event π (fun e => x e.1=b)+event π (fun e => y e.2=b)=s+2*d b := by
    change event π _+event π _=event π _+2*event π _
    rw [identity]
    unfold event
    rw [←avg_add]
    apply avg_congr
    intro e
    cases b <;> cases hx : x e.1 <;> cases hy : y e.2 <;> norm_num [hx,hy]
  have cs : z b+z (!b)≤1 := by
    dsimp [z]
    rw [Real.sqrt_mul (un _),Real.sqrt_mul (un _)]
    nlinarith only [Real.sq_sqrt (un b), Real.sq_sqrt (vn b),
      Real.sq_sqrt (un (!b)), Real.sq_sqrt (vn (!b)), uT, vT,
      sq_nonneg (Real.sqrt (u b)-Real.sqrt (v b)),
      sq_nonneg (Real.sqrt (u (!b))-Real.sqrt (v (!b)))]
  have amgm : 2*z b≤u b+v b := by
    dsimp [z]
    rw [Real.sqrt_mul (un _)]
    nlinarith [sq_nonneg (Real.sqrt (u b)-Real.sqrt (v b)),Real.sq_sqrt (un b),Real.sq_sqrt (vn b)]
  have lp : (27/50:ℝ)*u b≤event π (fun e => x e.1=b) := lowP _
  have lq : (27/50:ℝ)*v b≤event π (fun e => y e.2=b) := lowQ _
  exact _root_.PlanarUnitDistances.BinaryDiagonal.lighter (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hb cs hξ hs dsum (rect (fun p => x p=b) (fun q => y q=b))
    (rect (fun p => x p=(!b)) (fun q => y q=(!b))) (by linarith)

/-- Manuscript common-level comparison between the smaller edge-bit mass
and the two ordinary, independent conditional two-neighbor experiments. -/
theorem minority_le_variations (π : Law (P×Q)) {ξ : ℝ} (U : Law P) (V : Law Q)
    (rect : ∀ (A : P → Prop) (B : Q → Prop), event π (fun e => A e.1 ∧ B e.2) ≤
      let z := Real.sqrt (event U A*event V B)
      z*(z^(2/25:ℝ)+ξ))
    (lowP : ∀ A : P → Prop, (27/50:ℝ)*event U A≤event π (fun e => A e.1))
    (lowQ : ∀ B : Q → Prop, (27/50:ℝ)*event V B≤event π (fun e => B e.2))
    (hξ : 0≤ξ) (hs : ξ≤1/(2:ℝ)^100) (bit : P → Q → Bool) :
    min (event π (fun e => bit e.1 e.2=true)) (1-event π (fun e => bit e.1 e.2=true))≤10*(VP π bit+VQ π bit) := by
  let x (p : P) := majority (row π p) (bit p)
  let y (q : Q) := majority (col π q) (fun p => bit p q)
  let A (e : P×Q) := bit e.1 e.2≠x e.1
  let B (e : P×Q) := bit e.1 e.2≠y e.2
  have leftWrong : event π A≤VP π bit := by
    rw [←row_event π (fun p q => bit p q≠x p)]
    exact avg_mono _ (fun p => wrong_majority _ _)
  have rightWrong : event π B≤VQ π bit := by
    rw [←col_event π (fun p q => bit p q≠y q)]
    exact avg_mono _ (fun q => wrong_majority _ _)
  have bad : event π (fun e => A e ∨ B e)≤VP π bit+VQ π bit :=
    (event_union_le π A B).trans (add_le_add leftWrong rightWrong)
  have s : event π (fun e => x e.1≠y e.2)≤VP π bit+VQ π bit := by
    apply le_trans _ bad
    apply event_mono
    intro e h
    dsimp only [A,B]
    by_contra! hh
    exact h (hh.1.symm.trans hh.2)
  obtain ⟨b,hb⟩ := lighter_label π U V rect lowP lowQ hξ hs x y
  have mi : min (event π (fun e => bit e.1 e.2=true)) (1-event π (fun e => bit e.1 e.2=true))≤event π (fun e => bit e.1 e.2=b) := by
    cases b with
    | true => exact min_le_left .. 
    | false =>
      rw [event_congr π (P:=fun e => bit e.1 e.2=false) (Q:=fun e => ¬bit e.1 e.2=true)
        (fun e => by cases bit e.1 e.2 <;> decide),event_compl]
      exact min_le_right ..
  have incl := event_mono (μ:=π) (P:=fun e => bit e.1 e.2=b)
    (Q:=fun e => (x e.1=b ∧ y e.2=b) ∨ (A e ∨ B e)) (fun e h => by
      dsimp only [A,B]
      by_cases a : bit e.1 e.2=x e.1
      · by_cases c : bit e.1 e.2=y e.2
        · exact Or.inl ⟨a.symm.trans h,c.symm.trans h⟩
        · exact Or.inr (Or.inr c)
      · exact Or.inr (Or.inl a))
  have cover := incl.trans (event_union_le π _ _)
  linarith

end
end OAI.PlanarUnitDistances.BinaryMinority
