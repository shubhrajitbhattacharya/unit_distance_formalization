import PlanarUnitDistances.HeightNormalization
import PlanarUnitDistances.Matching

namespace PlanarUnitDistances.HeightTransfer
open Finset Real OAI.PlanarUnitDistances.LocalHeightTransfer
open scoped Classical
noncomputable section

private lemma complement_mass {A : Type*} [Fintype A] (m : A → ℝ) (hm : ∑ i, m i = 1)
    (F : A → Prop) : labelEvent m (fun i => ¬F i) = 1 - labelEvent m F := by
  rw [eq_sub_iff_add_eq,← hm]
  simp only [labelEvent,← sum_add_distrib]
  exact sum_congr rfl fun i _ => by by_cases h : F i <;> simp [h]

private lemma fiber_mass_total {A L : Type*} [Fintype A] [Fintype L] (m : A → ℝ)
    (h : ∑ i, m i = 1) (f : A → L) : ∑ j, labelEvent m (fun i => f i = j) = 1 := by
  simp only [labelEvent]
  rw [sum_comm]
  simpa only [Finset.sum_ite_eq, mem_univ, if_true] using h

private lemma fiber_nonneg {A : Type*} [Fintype A] {m : A → ℝ} (hm : ∀ i, 0 ≤ m i)
    (F : A → Prop) : 0 ≤ labelEvent m F :=
  sum_nonneg fun i _ => by split <;> simp_all

private lemma pair_disagreement {P L : Type*} [Fintype P] [Fintype L]
    (m : P → ℝ) (hs : ∑ p, m p = 1) (f : P → L) :
    (∑ p, ∑ r, m p * m r * dis (f p) (f r)) =
      1 - ∑ a, (labelEvent m (fun p => f p = a))^2 := by
  have diag : (∑ a, (labelEvent m (fun p => f p = a))^2) =
      ∑ p, ∑ r, if f p = f r then m p*m r else 0 := by
    simp only [labelEvent,pow_two,mul_sum,sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro r _
    rw [sum_comm]
    apply sum_congr rfl
    intro p _
    simp only [ite_mul,zero_mul,mul_ite,mul_zero,sum_ite_eq,mem_univ,if_true]
    by_cases he : f p = f r
    · simp [he, mul_comm]
    · simp [he, Ne.symm he]
  rw [diag,eq_sub_iff_add_eq,← sum_add_distrib]
  calc
    _ = ∑ p, ∑ r, m p*m r := by
      apply sum_congr rfl
      intro p _
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro r _
      by_cases h : f p = f r <;> simp [dis,h]
    _ = _ := by simp only [← mul_sum,hs,mul_one]

variable {P Q : Type} [Fintype P] [Fintype Q]

/-- The graph hypotheses used for coordinate transfer are precisely rectangle expansion
and the two lower marginal comparisons with the vertex counting distributions.
The distributions U,V may in fact be arbitrary probability laws. -/
theorem label_control_of_rectangles (w : P → Q → ℝ) (U : P → ℝ) (V : Q → ℝ)
    (hw : ∀ p q, 0 ≤ w p q) (hs : ∑ p, ∑ q, w p q = 1)
    (hU : ∀ p, 0 ≤ U p) (hV : ∀ q, 0 ≤ V q) (uSum : ∑ p, U p = 1) (vSum : ∑ q, V q = 1)
    {ξ : ℝ} (hξ : 0 ≤ ξ) (hξsmall : ξ ≤ 1/(2:ℝ)^100)
    (rect : ∀ (F : P → Prop) (G : Q → Prop),
      labelEvent (fun x : P × Q => w x.1 x.2) (fun x => F x.1 ∧ G x.2) ≤
      let b := sqrt (labelEvent U F * labelEvent V G)
      b*(b^(2/25:ℝ)+ξ))
    (lowP : ∀ (F : P → Prop), (27/50:ℝ)*labelEvent U F ≤
      labelEvent (fun x : P × Q => w x.1 x.2) (fun x => F x.1))
    (lowQ : ∀ (G : Q → Prop), (27/50:ℝ)*labelEvent V G ≤
      labelEvent (fun x : P × Q => w x.1 x.2) (fun x => G x.2)) :
    LabelControl 28 w := by
  intro L
  have hn : Nonempty P := by
    by_contra! he
    haveI : IsEmpty P := he
    simp at hs
  let T := Set.range L
  letI : Fintype T := Fintype.ofFinite _
  letI : Nonempty T := ⟨⟨L (.inl hn.some),Set.mem_range_self _⟩⟩
  let f (p : P) : T := ⟨L (.inl p),Set.mem_range_self _⟩
  let g (q : Q) : T := ⟨L (.inr q),Set.mem_range_self _⟩
  let m (x : P × Q) := w x.1 x.2
  let u (a : T) := labelEvent U (fun p => f p = a)
  let v (a : T) := labelEvent V (fun q => g q = a)
  have sm : ∑ x, m x = 1 := by rw [Fintype.sum_prod_type]; exact hs
  have cp (a : T) := complement_mass U uSum (fun p => f p = a)
  have cq (a : T) := complement_mass V vSum (fun q => g q = a)
  have hh := matching_for_edge_law m (fun x => f x.1) (fun x => g x.2) u v ξ
    (fun x => hw _ _) sm (fun a => fiber_nonneg hU _) (fun a => fiber_nonneg hV _)
    (fiber_mass_total U uSum f) (fiber_mass_total V vSum g) hξ hξsmall
    (fun a => rect (fun p => f p = a) (fun q => g q = a))
    (fun a => by simpa only [u,v,← cp,← cq] using rect (fun p => f p ≠ a) (fun q => g q ≠ a))
    (fun a => by simpa only [u,← cp] using lowP (fun p => f p ≠ a))
    (fun a => by simpa only [v,← cq] using lowQ (fun q => g q ≠ a))
  have marg (a : T) : labelEvent m (fun x => f x.1 = a) = labelEvent (left w) (fun p => f p = a) := by
    simp only [labelEvent,Fintype.sum_prod_type,m,left]
    apply sum_congr rfl
    intro p _
    by_cases h : f p = a <;> simp [h]
  have eqd : (∑ p, ∑ r, left w p * left w r * dis (L (.inl p)) (L (.inl r))) =
      1 - ∑ a, (labelEvent m (fun x => f x.1 = a))^2 := by
    simpa only [marg,dis,f,Subtype.mk.injEq] using pair_disagreement (left w) hs f
  rw [eqd]
  refine hh.2.1.trans_eq ?_
  congr 1
  simp only [labelEvent,Fintype.sum_prod_type,m,f,g,ne_eq,Subtype.mk.injEq,dis]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  split_ifs <;> simp_all

end
end PlanarUnitDistances.HeightTransfer
