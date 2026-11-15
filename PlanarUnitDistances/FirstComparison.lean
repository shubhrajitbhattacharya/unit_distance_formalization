import PlanarUnitDistances.ObservedMembership
import PlanarUnitDistances.CommonListSelection

namespace OAI.PlanarUnitDistances.CommonTemplate
open Finset FiniteLaw FiniteStarCoupling CrossSampling CrossStructure StrictCross
open ObservedMembership TemplateCoupling CrossPrediction
open scoped Classical
noncomputable section
variable {P Q A B H I L : Type*} [Fintype P] [Fintype Q] [Fintype A] [Fintype B]
  [Fintype H] [Fintype I] [Nonempty I] [Fintype L] [Nonempty L]

lemma mixture_left (π : Law (P×Q)) : mixture (right π) (col π) = left π := by
  apply law_ext; intro p
  simp only [mixture,left_val,avg,col_weight]

private lemma permitted_query (U : Finset (A×B)) (h : RestrictedTransfer.Permitted U) :
    ∃ q : Query A B, ∀ x, accepts q x ↔ x∈U := by
  rcases h with ⟨a,rfl⟩ | ⟨b,rfl⟩ | hc
  · exact ⟨.row a, fun _ => by simp [accepts,RestrictedTransfer.row]⟩
  · exact ⟨.col b, fun _ => by simp [accepts,RestrictedTransfer.col]⟩
  · exact ⟨.few U hc, fun _ => Iff.rfl⟩

def inconsistency (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B) :=
  event π (fun pq => ¬Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))

/-- A single common level with an actual iid center list and the original edge
law. The common row, column or two-atom restriction is constructed internally. -/
theorem first_comparison (π : Law (P×Q)) (h : P → H) (hp : ∀p,0<(left π).val p)
    (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B)
    {ζ u : ℝ} (hζ : 0<ζ) (hu : 0<u) :
    let a := listLaw (I := I) π h
    (avg (templates π a) (fun θ => VP (slice π a θ) bit)+VQ π bit)/6 ≤
      avg (templates π a) (fun θ => DP (slice π a θ) bit y)+DQ π bit x +
      16*(inconsistency π bit x y+predictionError π h x y/ζ+
        16/((Fintype.card I:ℝ)*u^2)+3*(ζ+u)+4/(Fintype.card L:ℝ)+
        Real.sqrt 2*hashNorm (C := L) (right π) (col π) h x) := by
  let a := listLaw (I := I) π h
  let ν := posteriorState π h x
  let νH := historyLaw π h
  let Y := candidates (I := I) ν ζ
  let ok := fun q => accurate (I := I) (νH q) ν u
  choose U perm shape margin using list_choice (I := I) ν hζ.le hu.le
  have choice (θ : I → H) : ∃ query : Query A B, U θ ≠ univ → ∀z, accepts query z ↔ z∈U θ := by
    by_cases hs : U θ=univ
    · exact ⟨.few ∅ (by simp),fun hn => (hn hs).elim⟩
    obtain ⟨v,he⟩ := permitted_query (U θ) ((perm θ).resolve_left hs)
    exact ⟨v, fun _ => he⟩
  choose qr hqr using choice
  let good (θ : I → H) (p : P) (q : Q) :=
    Consistent (bit p q) (x p) (y q) ∧ y q∈Y θ ∧ ok q θ ∧ x p∈U θ
  have localScore := aggregate_score π a bit x y Y U good shape (fun _ _ _ hg => ⟨hg.2.2.2,hg.2.1,hg.1⟩)
  let ρ : Law ((P×Q)×(I→H)) := joint π a
  have disint (f : P → Q → (I→H) → ℝ) :
      avg ρ (fun z => f z.1.1 z.1.2 z.2) =
      avg (right π) (fun q => avg (a q) (fun θ => avg (col π q) (fun p => f p q θ))) := by
    rw [show avg ρ (fun z => f z.1.1 z.1.2 z.2) = avg π (fun pq => avg (a pq.2) (fun θ => f pq.1 pq.2 θ)) from dependent_avg ..,
      ←col_avg π (fun p q => avg (a q) (fun θ => f p q θ))]
    exact avg_congr _ (fun q => avg_comm ..)
  let B₀ (z : (P×Q)×(I→H)) := ¬Consistent (bit z.1.1 z.1.2) (x z.1.1) (y z.1.2)
  let B₁ (z : (P×Q)×(I→H)) := y z.1.2 ∉ Y z.2
  let B₂ (z : (P×Q)×(I→H)) := ¬ok z.1.2 z.2
  let B₃ (z : (P×Q)×(I→H)) := ok z.1.2 z.2 ∧ U z.2 ≠ univ ∧ x z.1.1 ∉ U z.2
  have union := (event_mono ρ (P := fun z => ¬good z.2 z.1.1 z.1.2)
    (Q := fun z => ((B₀ z ∨ B₁ z) ∨ B₂ z) ∨ B₃ z) (by
    intro z hz
    by_cases hc : Consistent (bit z.1.1 z.1.2) (x z.1.1) (y z.1.2)
    · by_cases hy : y z.1.2∈Y z.2
      · by_cases ho : ok z.1.2 z.2
        · have hn : x z.1.1∉U z.2 := fun he => hz ⟨hc,hy,ho,he⟩
          exact Or.inr ⟨ho,fun he => hn (he ▸ mem_univ _),hn⟩
        · exact Or.inl (Or.inr ho)
      · exact Or.inl (Or.inl (Or.inr hy))
    · exact Or.inl (Or.inl (Or.inl hc))))
  have total : event ρ (fun z => ¬good z.2 z.1.1 z.1.2) ≤ event ρ B₀+event ρ B₁+event ρ B₂+event ρ B₃ := by
    linarith [event_union_le ρ (fun z => (B₀ z ∨ B₁ z) ∨ B₂ z) B₃,
      event_union_le ρ (fun z => B₀ z ∨ B₁ z) B₂,event_union_le ρ B₀ B₁]
  have evdis (f : P → Q → (I→H) → Prop) :
      event ρ (fun z => f z.1.1 z.1.2 z.2) =
      avg (right π) (fun q => avg (a q) (fun θ => event (col π q) (fun p => f p q θ))) := by
    unfold event
    exact disint (fun p q θ => @ite ℝ (f p q θ) (Classical.propDecidable _) 1 0)
  have listOnly (f : Q → (I→H) → Prop) : event ρ (fun z => f z.1.2 z.2) =
      avg (right π) (fun q => event (a q) (f q)) := by
    rw [evdis (fun _ q θ => f q θ)]
    apply avg_congr; intro q
    unfold event
    apply avg_congr; intro θ
    by_cases hh : f q θ <;> simp [hh,avg_const]
  have m₀ : event ρ B₀ = inconsistency π bit x y := by
    unfold event inconsistency
    change avg (dependent π _) _ = _
    rw [dependent_avg]
    unfold event
    apply avg_congr; intro pq
    by_cases hc : Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2) <;> simp [B₀,hc,avg_const]
  have m₁ : event ρ B₁ ≤ predictionError π h x y/ζ := by
    rw [listOnly (fun q θ => y q∉Y θ)]
    have omitted (q : Q) := omitted_center (I := I) (νH q) ν (y q) hζ
    apply (avg_mono (right π) omitted).trans_eq
    have sub (q : Q) : 1 - avg (νH q) (fun t => crossMass (ν t) (y q)) =
        avg (col π q) (fun p => 1-crossMass (ν (h p)) (y q)) := by
      rw [avg_sub,avg_const]; simp [νH,historyLaw,push_avg]
    simp_rw [sub,div_eq_inv_mul,avg_smul]
    rw [col_avg]
    rfl
  have m₂ : event ρ B₂ ≤ 16/((Fintype.card I:ℝ)*u^2) := by
    rw [listOnly (fun q θ => ¬ok q θ)]
    exact avg_le_const _ (fun q => empirical_list_failure (νH q) ν u hu)
  let active (q : Q) (θ : I→H) := ok q θ ∧ U θ≠univ
  have m₃ : event ρ B₃ ≤ 3*(ζ+u)+4/(Fintype.card L:ℝ)+
      Real.sqrt 2*hashNorm (C := L) (right π) (col π) h x := by
    have re : event ρ B₃ = rejectChance (right π) (col π) x a active (fun _ => qr) := by
      unfold rejectChance
      rw [evdis (fun p q θ => ok q θ ∧ U θ≠univ ∧ x p∉U θ)]
      apply avg_congr; intro q
      apply avg_congr; intro θ
      apply event_congr; intro p
      by_cases hu' : U θ=univ
      · simp [active,hu']
      · simp only [active,hqr θ hu']
        by_cases ho : ok q θ <;> simp [ho]
    rw [re]
    apply reject_bound (L := L) _ _ (by rwa [mixture_left]) _ _ _ _ _ (by positivity)
    intro q θ hg
    have hm := margin θ (νH q) hg.1
    have he := event_compl (mix (νH q) ν) (fun z => z∈U θ)
    have bd : event (mix (νH q) ν) (fun z => z∉U θ) ≤ 3*(ζ+u) := by linarith
    unfold event at bd ⊢
    rw [mix_avg] at bd
    simp only [νH,historyLaw,push_avg,ν,posteriorState] at bd
    simp_rw [mixture_left, hqr θ hg.2]
    apply le_trans _ bd
    apply avg_mono; intro p
    apply avg_mono; intro r
    by_cases hh : x r∈U θ <;> simp [hh]
  have eqg : event ρ (fun z => ¬good z.2 z.1.1 z.1.2) =
      avg π (fun pq => event (a pq.2) (fun θ => ¬good θ pq.1 pq.2)) := dependent_avg .. 
  rw [m₀,eqg] at total
  dsimp only
  linarith only [localScore,total,m₁,m₂,m₃]

end
end OAI.PlanarUnitDistances.CommonTemplate
