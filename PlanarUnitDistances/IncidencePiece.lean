import PlanarUnitDistances.WinningGraph
import PlanarUnitDistances.WalkBudget
open Filter OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
namespace PlanarUnitDistances
noncomputable section

/-- Proposition cb:finite-piece on the actual Euclidean uniform unit-edge law.
P and Q are both subsets of the same specialized input. The information,
expansion, and individual degrees/marginals all concern these same two sets. -/
theorem fixed_incidence_piece {g : ℝ} (hg : 0<g) (ha1 : 10000*g≤1/10) :
    let a := 10000*g
    ∀ᶠ t : ℝ in atTop, ∀ X : Finset Plane, (X.card:ℝ)=t^3 →
      t^(4-g) ≤ ((orderedPairs X).card:ℝ) →
      ∃ P ⊆ X, ∃ Q ⊆ X,
        t^(1+2*a-173*g) ≤ (P.card:ℝ) ∧ (P.card:ℝ) ≤ 2*t^(1+2*a) ∧
        (Q.card:ℝ) ≤ t^(2+a) ∧ t^(2+2*a-90*g) ≤ incidences P Q ∧
        (∀ p ∈ P, (27/100:ℝ)*t^(1-90*g) ≤ degree Q p ∧ degree Q p ≤ t^(1+10*g) ∧
          (27/50:ℝ)/P.card ≤ degree Q p/incidences P Q ∧
          degree Q p/incidences P Q ≤ t^(-1-2*a+100*g)) ∧
        t^(-1-2*a+100*g) ≤ t^(-1:ℝ) ∧
        (∀ q ∈ Q, (27/50:ℝ)*t^(a-90*g) ≤ degree P q ∧ degree P q ≤ t^(a+10*g) ∧
          (27/50:ℝ)/Q.card ≤ degree P q/incidences P Q) ∧
        (∀ A ⊆ P, ∀ B ⊆ Q,
          let z := (A.card:ℝ)/P.card*((B.card:ℝ)/Q.card)
          incidences A B/incidences P Q ≤ Real.sqrt z*(z^(1/25:ℝ)+t^(-150*g))) ∧
        unitWalkInformation P Q+1 ≤ 10200*g*Real.log t := by
  let a := 10000*g
  filter_upwards [fixed_winning_graph hg ha1,fixed_information_bound hg ha1,
    eventually_ge_atTop (1:ℝ)] with t hwin hbudget ht
  have ht0 := zero_lt_one.trans_le ht
  intro X hcard hdense
  obtain ⟨P,hPX,Q,hQX,hm,hm',hn,he,hp,hq,hexp⟩ := hwin X hcard hdense
  have hm0 : 0<(P.card:ℝ) := (Real.rpow_pos_of_pos ht0 _).trans_le hm
  have he0 : 0 < incidences P Q := (Real.rpow_pos_of_pos ht0 _).trans_le he
  have hn0 : 0<(Q.card:ℝ) := pos_of_mul_pos_right
    (he0.trans_le (incidences_le P Q)) (Nat.cast_nonneg _)
  have low (k x b c : ℝ) (hk : 0<k) (hcap : k≤c*t^b) (hc : 0<c)
      (hx : (27/50:ℝ)/k ≤ x/incidences P Q) :
      ((27/50:ℝ)/c)*t^(2+2*a-90*g-b) ≤ x := by
    have hmult := (le_div_iff₀ he0).mp hx
    have hden := div_le_div_of_nonneg_left (by norm_num : 0≤(27/50:ℝ)) hk hcap
    have hboth := mul_le_mul hden he (Real.rpow_nonneg ht0.le _) (div_nonneg (by norm_num) hk.le)
    apply le_trans _ (hboth.trans hmult)
    dsimp only [a]
    rw [Real.rpow_sub ht0]
    field_simp [(Real.rpow_pos_of_pos ht0 b).ne',hc.ne']
    ring_nf
    exact le_rfl
  have lowP (p : Plane) (hpP : p∈P) : (27/100:ℝ)*t^(1-90*g)≤degree Q p := by
    have hh := low _ _ (1+2*a) 2 hm0 hm' (by norm_num) (hp p hpP).2
    simpa only [show (27/50:ℝ)/2=27/100 by norm_num,show 2+2*a-90*g-(1+2*a)=1-90*g by ring] using hh
  have lowQ (q : Plane) (hqQ : q∈Q) : (27/50:ℝ)*t^(a-90*g)≤degree P q := by
    have hh := low _ _ (2+a) 1 hn0 (by simpa only [one_mul] using hn) (by norm_num) (hq q hqQ).2
    simpa only [div_one,show 2+2*a-90*g-(2+a)=a-90*g by ring] using hh
  have upperP (p : Plane) (hpP : p∈P) : degree Q p/incidences P Q ≤ t^(-1-2*a+100*g) := by
    have hh := div_le_div₀ (Real.rpow_nonneg ht0.le _) (hp p hpP).1 (Real.rpow_pos_of_pos ht0 _) he
    rw [←Real.rpow_sub ht0] at hh
    exact hh.trans_eq (congrArg (fun x : ℝ => t^x) (by dsimp [a]; ring))
  have hinfo := unitWalkInformation_bound P Q (Finset.card_pos.mp (Nat.cast_pos.mp hm0))
    (d:=(27/50:ℝ)*t^(a-90*g)) (by positivity) he0 lowQ
    (fun p hpP => (show 0<(27/100:ℝ)*t^(1-90*g) by positivity).trans_le (lowP p hpP))
  refine ⟨P,hPX,Q,hQX,hm,hm',hn,he,?_,?_,?_,hexp,?_⟩
  · exact fun p hpP => ⟨lowP p hpP,(hp p hpP).1,(hp p hpP).2,upperP p hpP⟩
  · apply Real.rpow_le_rpow_of_exponent_le ht; linarith
  · exact fun q hqQ => ⟨lowQ q hqQ,(hq q hqQ).1,(hq q hqQ).2⟩
  · exact hbudget hm0 (Nat.cast_nonneg _) hm' hn he hinfo


/-- The unrestricted real-input and real-algebraic-output version of cb:finite-piece. -/
theorem algebraic_incidence_piece {g : ℝ} (hg : 0<g) (ha1 : 10000*g≤1/10) :
    let a := 10000*g
    ∀ᶠ t : ℝ in atTop, ∀ X : Finset Plane, (X.card:ℝ)=t^3 →
      t^(4-g) ≤ ((orderedPairs X).card:ℝ) →
      ∃ P Q : Finset Plane,
        (∀ p ∈ P, ∀ i, IsAlgebraic ℚ (p i)) ∧ (∀ q ∈ Q, ∀ i, IsAlgebraic ℚ (q i)) ∧
        t^(1+2*a-173*g) ≤ (P.card:ℝ) ∧ (P.card:ℝ) ≤ 2*t^(1+2*a) ∧
        (Q.card:ℝ) ≤ t^(2+a) ∧ t^(2+2*a-90*g) ≤ incidences P Q ∧
        (∀ p ∈ P, (27/100:ℝ)*t^(1-90*g) ≤ degree Q p ∧ degree Q p ≤ t^(1+10*g) ∧
          (27/50:ℝ)/P.card ≤ degree Q p/incidences P Q ∧
          degree Q p/incidences P Q ≤ t^(-1-2*a+100*g)) ∧
        t^(-1-2*a+100*g) ≤ t^(-1:ℝ) ∧
        (∀ q ∈ Q, (27/50:ℝ)*t^(a-90*g) ≤ degree P q ∧ degree P q ≤ t^(a+10*g) ∧
          (27/50:ℝ)/Q.card ≤ degree P q/incidences P Q) ∧
        (∀ A ⊆ P, ∀ B ⊆ Q,
          let z := (A.card:ℝ)/P.card*((B.card:ℝ)/Q.card)
          incidences A B/incidences P Q ≤ Real.sqrt z*(z^(1/25:ℝ)+t^(-150*g))) ∧
        unitWalkInformation P Q+1 ≤ 10200*g*Real.log t := by
  filter_upwards [fixed_incidence_piece hg ha1] with t hpiece
  intro X hc hXdense
  obtain ⟨Y,hcard,hXY,hAlg⟩ := algebraic_set_specialization X
  have hdense : t^(4-g) ≤ ((orderedPairs Y).card:ℝ) := by
    apply hXdense.trans
    exact_mod_cast (by rw [orderedPairs_card,orderedPairs_card]; omega :
      (orderedPairs X).card ≤ (orderedPairs Y).card)
  obtain ⟨P,hP,Q,hQ,hpiece⟩ := hpiece Y (by rwa [hcard]) hdense
  exact ⟨P,Q,fun p hp => hAlg p (hP hp),fun q hq => hAlg q (hQ hq),hpiece⟩

end
end PlanarUnitDistances
