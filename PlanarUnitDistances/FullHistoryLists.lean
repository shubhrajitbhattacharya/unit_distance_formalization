import PlanarUnitDistances.ExactHistorySize
import PlanarUnitDistances.Information
import PlanarUnitDistances.ProofAssembly

namespace PlanarUnitDistances.ComparisonConstants
open Real Filter Finset OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open scoped Topology Classical
noncomputable section

/-- The actual space of ordered lists of k histories, each history recording
the pair of coarse colors, even if the same history repeats in the list. -/
abbrev FullList (n : ℕ) := Fin (2^18000) → FiniteInformation.History (Fin (2^144000) × Fin (2^144000)) n

private theorem list_gap : ((2:ℝ)^594000*exactGap)*(30600*288000) ≤ 1/4 := by
  have hg := exactGap_lt_largeHeightGap.le
  rw [Real.rpow_neg (by norm_num),←Nat.cast_ofNat (R:=ℝ) (n:=594036),Real.rpow_natCast] at hg
  change exactGap≤dy 594036 at hg
  have hd : (2:ℝ)^594000*dy 594036=dy 36 := by
    rw [←div 594036 594000 (by decide),div_eq_mul_inv,
      show (dy 594000)⁻¹=(2:ℝ)^594000 from inv_inv _,mul_comm]
  calc
    _ ≤ ((2:ℝ)^594000*dy 594036)*(30600*288000) := by gcongr
    _ = dy 36*(30600*288000) := by rw [hd]
    _ ≤ _ := by norm_num [dy]

/-- The size of the whole list, with the exact saving and unrounded
ceiling. The strict prefix length removes the manuscript's extra factor two. -/
theorem full_list_card {t D : ℝ} (ht : 1≤t) (hi : D+1≤30600*exactGap*log t)
    {n : ℕ} (hn : n<historyDepth D) : (Fintype.card (FullList n):ℝ) ≤ t^(1/4:ℝ) := by
  let k := (2:ℝ)^18000
  let L := (2:ℝ)^144000
  have ht' : 0<t := zero_lt_one.trans_le ht
  have idx : (n:ℝ)≤(2:ℝ)^576000*(D+1) := (Nat.lt_ceil.mp hn).le
  have lk : log 2≤1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have coeff : k*(n:ℝ)*(288000*log 2) ≤ (1/4)*log t := calc
    _ ≤ k*(n:ℝ)*288000 := mul_le_mul_of_nonneg_left (by linarith only [lk]) (by dsimp [k]; positivity)
    _ ≤ k*((2:ℝ)^576000*(30600*exactGap*log t))*288000 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (idx.trans (mul_le_mul_of_nonneg_left hi (by positivity))) (by dsimp [k]; positivity)) (by norm_num)
    _ = (((2:ℝ)^594000*exactGap)*(30600*288000))*log t := by
      rw [show (2:ℝ)^594000=(2:ℝ)^18000*(2:ℝ)^576000 from pow_add 2 18000 576000]
      dsimp only [k]; ac_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right list_gap (log_nonneg ht)
  have card : (Fintype.card (FullList n):ℝ) = ((L*L)^n)^(2^18000:ℕ) := by
    simp only [FullList,Fintype.card_fun,FiniteInformation.history_card,Fintype.card_prod,
      Fintype.card_fin,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat,L]
  have Lpos : 0<L := by dsimp [L]; positivity
  rw [card,←Real.exp_log (show 0<((L*L)^n)^(2^18000:ℕ) by positivity),
    Real.log_pow,Real.log_pow,Real.log_mul Lpos.ne' Lpos.ne',Real.rpow_def_of_pos ht',exp_le_exp]
  have logL : log L=144000*log 2 := Real.log_pow _ _
  rw [logL]
  push_cast
  change k*((n:ℝ)*(144000*log 2+144000*log 2))≤log t*(1/4)
  linarith only [coeff]

/-- At every point in the original incidence piece, the list-type factor
in the collision term divided by its actual degree is at most k^{-8}. -/
theorem eventual_full_list_collision :
    ∀ᶠt : ℝ in atTop, ∀(P Q : Finset Plane) (M : CommonFieldModel.Model P Q),
      ProofAssembly.LargePiece t P Q M → ∀n<historyDepth (unitWalkInformation P Q),
      (Fintype.card (FullList n):ℝ)≤t^(1/4:ℝ) ∧
      ∀p∈P,(Fintype.card (FullList n):ℝ)/degree Q p≤dy 144000 := by
  have hl := exactGap_lt_largeHeightGap.trans_le (Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1:ℝ)≤2) (by norm_num : -(594036:ℝ)≤ -32))
  have power : (3/4:ℝ) ≤ 1-90*(3*exactGap) := by norm_num [Real.rpow_neg] at hl; linarith
  have small := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).eventually
    (eventually_le_nhds (mul_pos (by norm_num : (0:ℝ)<27/100) (pos 144000)))
  filter_upwards [eventually_ge_atTop (1:ℝ),small] with t ht hs
  intro P Q M piece n hn
  obtain ⟨_,_,_,_,_,deg,_,_,_,info,_⟩ := piece
  have ip : unitWalkInformation P Q+1≤30600*exactGap*log t := by convert info using 1 <;> ring
  have cap := full_list_card ht ip hn
  refine ⟨cap,?_⟩
  intro p hp
  have ht' : 0<t := zero_lt_one.trans_le ht
  have ppos : 0<degree Q p := (mul_pos (by norm_num) (Real.rpow_pos_of_pos ht' _)).trans_le (deg p hp).1
  apply (div_le_iff₀ ppos).mpr
  calc
    _ ≤ t^(1/4:ℝ) := cap
    _ = t^(3/4:ℝ)*t^(-(1/2):ℝ) := by rw [←Real.rpow_add ht']; norm_num
    _ ≤ t^(1-90*(3*exactGap))*((27/100)*dy 144000) :=
      mul_le_mul (rpow_le_rpow_of_exponent_le ht power) hs (Real.rpow_nonneg ht'.le _) (Real.rpow_nonneg ht'.le _)
    _ = dy 144000*((27/100)*t^(1-90*(3*exactGap))) := by ac_rfl
    _ ≤ dy 144000*degree Q p := mul_le_mul_of_nonneg_left (deg p hp).1 (pos _).le

end
end PlanarUnitDistances.ComparisonConstants

