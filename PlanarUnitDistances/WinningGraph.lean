import PlanarUnitDistances.FixedCutting
import PlanarUnitDistances.WinningError

open Filter OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open OAI.PlanarUnitDistances.CircleCutting (cuttingLog)
open OAI.PlanarUnitDistances.GeometricOptimizer (exists_rectangle)

namespace PlanarUnitDistances
noncomputable section

/-- Simultaneously extract both marginal lower bounds and the stated size,
edge, and maximum-degree estimates on a single Euclidean unit-incidence graph. -/
theorem fixed_winning_graph {g : ℝ} (hg : 0<g) (ha1 : 10000*g≤1/10) :
    let a := 10000*g
    ∀ᶠ t : ℝ in atTop, ∀ X : Finset Plane, (X.card:ℝ)=t^3 →
      t^(4-g) ≤ ((orderedPairs X).card:ℝ) →
      ∃ F ⊆ X, ∃ G ⊆ X,
        t^(1+2*a-173*g) ≤ (F.card:ℝ) ∧ (F.card:ℝ) ≤ 2*t^(1+2*a) ∧
        (G.card:ℝ) ≤ t^(2+a) ∧ t^(2+2*a-90*g) ≤ incidences F G ∧
        (∀ p ∈ F, degree G p ≤ t^(1+10*g) ∧ (27/50:ℝ)/F.card ≤ degree G p/incidences F G) ∧
        (∀ q ∈ G, degree F q ≤ t^(a+10*g) ∧ (27/50:ℝ)/G.card ≤ degree F q/incidences F G) ∧
        (∀ A ⊆ F, ∀ B ⊆ G,
          let z := (A.card:ℝ)/F.card*((B.card:ℝ)/G.card)
          incidences A B/incidences F G ≤ Real.sqrt z*(z^(1/25:ℝ)+t^(-150*g))) := by
  let a := 10000*g
  filter_upwards [fixed_initial_rectangle hg ha1,fixed_winner_scales hg,winning_error_bound hg ha1,eventually_ge_atTop (1:ℝ)]
    with t htrim hsc herror ht
  have ht0 := zero_lt_one.trans_le ht
  have ha : 0<a := by dsimp [a]; positivity
  intro X hc hDense
  obtain ⟨P,hPX,Q,hQX,hm,hm',hn,hn',he,hdP,hdQ,hT,hraw⟩ := htrim X hc hDense
  have hm0 : 0<(P.card:ℝ) := (Real.rpow_pos_of_pos ht0 _).trans_le hm
  have hn0 : 0<(Q.card:ℝ) := (Real.rpow_pos_of_pos ht0 _).trans_le hn
  have he0 : 0 < incidences P Q := (Real.rpow_pos_of_pos ht0 _).trans_le he
  have hτ0 := Real.rpow_pos_of_pos ht0 (-a/8)
  have hτ1 : t^(-a/8) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith)
  obtain ⟨F,hFP,G,hGQ,hOpt⟩ := exists_rectangle P Q (t:=t) (a:=a) he0
    (cuttingLog_one_le X.card)
    (cuttingLog_mono (Finset.card_le_card hPX)) (cuttingLog_mono (Finset.card_le_card hQX))
    (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg ht0.le _) ht0 hdP hdQ hτ0 hτ1
  dsimp only at hOpt
  obtain ⟨hU,hV,_,hwin,hExp,hatF,hatG⟩ := hOpt
  let U : ℝ := F.card/(P.card:ℝ)
  let V : ℝ := G.card/(Q.card:ℝ)
  have hu0 : 0≤U := div_nonneg (Nat.cast_nonneg _) hm0.le
  have hv0 : 0≤V := div_nonneg (Nat.cast_nonneg _) hn0.le
  have hu1 : U≤1 := (div_le_one hm0).mpr (Nat.cast_le.mpr (Finset.card_le_card hFP))
  have hv1 : V≤1 := (div_le_one hn0).mpr (Nat.cast_le.mpr (Finset.card_le_card hGQ))
  have hr := hraw F hFP G hGQ
  have hy : t^(-1:ℝ)≤t^(-a) := Real.rpow_le_rpow_of_exponent_le ht (by dsimp [a]; linarith)
  have hb := trim_linear_terms hu0 hv0 (Real.rpow_pos_of_pos ht0 (20*g))
    (Real.rpow_nonneg ht0.le (-1)) hy hr.1 hr.2
  have hs : Real.sqrt (t^(-a))=t^(-a/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul ht0.le]; congr 1; ring
  rw [hs] at hb
  obtain ⟨_,hUVw,hUw,hVw,hWw,hFdel,hGdel⟩ := hsc hU hV hu1 hv1 hwin hb hm hn
  have hcoef0 := (OAI.PlanarUnitDistances.GeometricExpansion.factor_bounds (Nat.cast_nonneg P.card)
    (Nat.cast_nonneg Q.card) he0 (Real.rpow_nonneg ht0.le (1+10*g))
    (Real.rpow_nonneg ht0.le (a+10*g)) ht0 (a:=a) (L:=cuttingLog X.card)).1
  have hErr := herror (zero_le_one.trans hcoef0) hT hUw hVw hUVw hwin
  have hfcount := (le_div_iff₀ hm0).mp hUw
  have hcount := (mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg ht0.le (-160*g))).trans hfcount
  have hecount := (le_div_iff₀ he0).mp hWw
  have hedge := (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg ht0.le (-87*g))).trans hecount
  rw [← Real.rpow_add ht0] at hcount hedge
  refine ⟨F,hFP.trans hPX,G,hGQ.trans hQX,?_,
    (Nat.cast_le.mpr (Finset.card_le_card hFP)).trans hm',
    (Nat.cast_le.mpr (Finset.card_le_card hGQ)).trans hn',?_,?_,?_,?_⟩
  · simpa only [show -160*g+(1+2*(10000*g)-13*g)=1+2*(10000*g)-173*g by ring] using hcount
  · simpa only [show -87*g+(2+2*(10000*g)-3*g)=2+2*(10000*g)-90*g by ring] using hedge
  · exact fun p hp => ⟨(degree_mono hGQ p).trans (hdP p (hFP hp)),hatF hFdel p hp⟩
  · exact fun q hq => ⟨(degree_mono hFP q).trans (hdQ q (hGQ hq)),hatG hGdel q hq⟩
  · intro A hA B hB
    exact (hExp A hA B hB).trans (mul_le_mul_of_nonneg_left (add_le_add_right hErr _) (Real.sqrt_nonneg _))

end
end PlanarUnitDistances
