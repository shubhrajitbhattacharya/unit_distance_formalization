import PlanarUnitDistances.IntegratedScores
import PlanarUnitDistances.ComparisonConstants

namespace OAI.PlanarUnitDistances.CommonTemplate
open Finset FiniteLaw FiniteStarCoupling MeasureTheory
open _root_.PlanarUnitDistances.ComparisonConstants
open scoped Classical
noncomputable section
variable {P Q A B I L Ω : Type*} [Fintype P] [Fintype Q] [Fintype A] [Fintype B]
  [Fintype I] [Nonempty I] [Fintype L] [Nonempty L]
  [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B] [MeasurableSingletonClass B]
  [MeasurableSpace Ω]

lemma fourth_root_bound {D : ℝ} {K : ℕ} (hD : 0≤D) (hK : 0<K)
    (hk : (2:ℝ)^576000*(D+1) ≤ (K:ℝ)) : (D/(K:ℝ))^(1/4:ℝ) ≤ dy 144000 := by
  have hu := mul_le_mul_of_nonneg_left hk (pos 576000).le
  have he : dy 576000*((2:ℝ)^576000*(D+1))=D+1 := by
    rw [←mul_assoc]
    change ((2:ℝ)^576000)⁻¹*(2:ℝ)^576000*(D+1)=D+1
    rw [inv_mul_cancel₀ (pow_ne_zero _ (two_ne_zero : (2:ℝ)≠0)),one_mul]
  rw [he] at hu
  have cut := (div_le_iff₀ (Nat.cast_pos.mpr hK : (0:ℝ)<K)).mpr (le_trans (le_add_of_nonneg_right zero_le_one) hu)
  apply le_of_pow_le_pow_left₀ (n := 4) (by decide) (pos _).le
  rw [show (1/4:ℝ)=((4:ℕ):ℝ)⁻¹ from by norm_num,Real.rpow_inv_natCast_pow
    (div_nonneg hD (Nat.cast_nonneg _)) (by decide),_root_.PlanarUnitDistances.ComparisonConstants.pow]
  exact cut

/-- The literal common-level conclusions with the paper's 16e₀S losses, using
the actual conditional experiment T from this very same observation history. -/
theorem exact_common_scores (π : Law (P×Q)) (hp : ∀p,0<(left π).val p)
    (σ : Measure Ω) [IsFiniteMeasure σ] (hσ : 0<σ.real Set.univ)
    (t : Ω → CommonLevel P Q A B) (h₁ : ∀p,Measurable (fun j => (t j).x p))
    (h₂ : ∀q,Measurable (fun j => (t j).y q)) (h₃ : ∀p q,Measurable (fun j => (t j).bit p q))
    (K : ℕ) (hK : 0<K) (hD : 0≤commonInformation π)
    (hk : (2:ℝ)^576000*(commonInformation π+1) ≤ (K:ℝ))
    (Icard : (Fintype.card I:ℝ)=(2:ℝ)^18000) (Lcard : ((Fintype.card L:ℝ))⁻¹=dy 144000)
    {S : ℝ} (hS : 2^2100<S) (hW : σ.real Set.univ ≤ S/dy 1800)
    (hM : (∫ j, inconsistency π (t j).bit (t j).x (t j).y ∂σ) ≤ 4) :
    ∃ n<K, ∃ h : P → FiniteInformation.History (L×L) n,
      (univ.image h).card ≤ (Fintype.card L)^(2*(K-1)) ∧
      ((∫j, cvT (I := I) π h (t j) ∂σ)+(∫j, VQ π (t j).bit ∂σ))/6 ≤
        (∫j, cdT (I := I) π h (t j) ∂σ)+(∫j, DQ π (t j).bit (t j).x ∂σ)+16*(dy 144*S) ∧
      (∫j, VP π (t j).bit ∂σ)/6 ≤ (∫j, DP π (t j).bit (t j).y ∂σ)+
        (∫j, posteriorMoment π h (t j) ∂σ)+16*(dy 144*S) := by
  let W := σ.real Set.univ
  let m := levelMean σ (fun j => inconsistency π (t j).bit (t j).x (t j).y)
  let R := (commonInformation π/(K:ℝ))^(1/4:ℝ)
  let E := W*(m+4*dy 144000+4*Real.sqrt 3*Real.sqrt 6*R)
  have hm : W*m ≤ 4 := by
    dsimp only [W,m,levelMean]
    rwa [mul_div_cancel₀ _ hσ.ne']
  have hr := fourth_root_bound hD hK hk
  have B := budgets hS hσ.le hW hm hr (M:=W*m) (E:=E) (by change W*(m+4*dy 144000+4*Real.sqrt 3*Real.sqrt 6*R) ≤ W*m+W*(4*dy 144000+4*Real.sqrt 3*Real.sqrt 6*R); exact le_of_eq (by ring))
  obtain ⟨n,hn,h,sz,_,hA,hB⟩ := continuum_scores (I := I) (L := L) π hp σ hσ t h₁ h₂ h₃ K hK (pos 1946) (pos 4501)
  have hL : 4/(Fintype.card L:ℝ)=4*dy 144000 := by rw [div_eq_mul_inv,Lcard]
  rw [Icard,hL] at hA
  rw [hL] at hB
  let a := m+4*dy 144000+4*Real.sqrt 3*Real.sqrt 6*R
  let extras := 16/((2:ℝ)^18000*(dy 4501)^2)+3*(dy 1946+dy 4501)+4*dy 144000+4*Real.sqrt 6*R
  have Ba : W*(m+a/dy 1946+extras) ≤ dy 144*S := by
    apply le_trans _ B.1
    change W*(m+a/dy 1946+extras) ≤ W*m+E/dy 1946+W*extras
    rw [mul_add,mul_add,← mul_div_assoc]
  have Bb : W*(m+a/dy 1946+dy 1946) ≤ dy 144*S := by
    apply le_trans _ B.2
    dsimp only [a,E]
    apply le_of_eq
    ring
  have unweight (f : Ω → ℝ) : W*levelMean σ f = ∫j,f j ∂σ := by
    dsimp only [W,levelMean]
    exact mul_div_cancel₀ _ hσ.ne'
  refine ⟨n,hn,h,sz,?_,?_⟩
  · have hg : (levelMean σ (fun j => cvT (I := I) π h (t j))+levelMean σ (fun j => VQ π (t j).bit))/6 ≤
        levelMean σ (fun j => cdT (I := I) π h (t j))+levelMean σ (fun j => DQ π (t j).bit (t j).x) +
        16*(m+a/dy 1946+extras) := by
      apply hA.trans_eq
      change _+_+16*(m+a/dy 1946+_+_+_+_) = _+_+16*(m+a/dy 1946+extras)
      dsimp only [extras,R]
      ac_rfl
    have hu := mul_le_mul_of_nonneg_left hg hσ.le
    change W*_ ≤ W*_ at hu
    rw [←mul_div_assoc,mul_add,unweight,unweight,mul_add,mul_add,unweight,unweight,
      mul_left_comm W 16] at hu
    exact hu.trans (add_le_add_right (mul_le_mul_of_nonneg_left Ba (by norm_num : (0:ℝ)≤16)) _)
  · change _ ≤ _ + _ + 16*(m+a/dy 1946+dy 1946) at hB
    have hu := mul_le_mul_of_nonneg_left hB hσ.le
    change W*_ ≤ W*_ at hu
    rw [←mul_div_assoc,unweight,mul_add,mul_add,unweight,unweight,mul_left_comm W 16] at hu
    exact hu.trans (add_le_add_right (mul_le_mul_of_nonneg_left Bb (by norm_num : (0:ℝ)≤16)) _)

end
end OAI.PlanarUnitDistances.CommonTemplate

