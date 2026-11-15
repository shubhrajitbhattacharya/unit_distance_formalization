import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace PlanarUnitDistances.ComparisonConstants
open Real
noncomputable section

/-- The literal real number 2 to the power minus n. Avoid evaluating
the manuscript's large dyadic powers during checking. -/
def dy (n : ℕ) : ℝ := ((2:ℝ)^n)⁻¹
lemma pos (n : ℕ) : 0<dy n := by unfold dy; positivity
lemma antitone {m n : ℕ} (h : m≤n) : dy n≤dy m := by
  apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
  exact pow_le_pow_right₀ (by norm_num) h
lemma mul (n m : ℕ) : dy n*dy m=dy (n+m) := by simp only [dy,pow_add,mul_inv_rev]; ring
lemma div (n m : ℕ) (h : m≤n) : dy n/dy m = dy (n-m) := by
  apply (div_eq_iff (pos _).ne').mpr
  rw [mul,Nat.sub_add_cancel h]
lemma pow (n m : ℕ) : dy n^m=dy (n*m) := by simp [dy,inv_pow,pow_mul]

set_option maxRecDepth 1000 in
/-- Literal comparison budget. Here W is the common width, M the integrated
edge inconsistency, E the integrated predicted rejection and R the
prediction fourth root. All are in unnormalized width units except R. -/
theorem budgets {S W M E R : ℝ} (hS : 2^2100 < S) (hW : 0≤W)
    (hW' : W ≤ S/dy 1800) (hM : M≤4)
    (hR : R≤dy 144000)
    (hE : E≤M+W*(4*dy 144000+4*sqrt 3*sqrt 6*R)) :
    M+E/dy 1946+W*(16/((2:ℝ)^18000*(dy 4501)^2)+3*(dy 1946+dy 4501)+4*dy 144000+4*sqrt 6*R)
      ≤ dy 144*S ∧ M+E/dy 1946+W*dy 1946 ≤ dy 144*S := by
  have hs : 0<S := (pow_pos (by norm_num : (0:ℝ)<2) 2100).trans hS
  have k0 : (4:ℝ) ≤ S*(4*dy 2100) := by
    have hh := mul_le_mul_of_nonneg_right hS.le (mul_nonneg (by norm_num : (0:ℝ)≤4) (pos 2100).le)
    have ee : (2:ℝ)^2100*(4*dy 2100) = 4 := by
      calc
        _ = 4*((2:ℝ)^2100 * ((2:ℝ)^2100)⁻¹) := by unfold dy; ac_rfl
        _ = 4 := by rw [mul_inv_cancel₀ (pow_ne_zero _ (two_ne_zero : (2:ℝ)≠0)),mul_one]
    rwa [ee] at hh
  have k1 : (4:ℝ)*sqrt 3*sqrt 6 ≤18 := by
    rw [mul_assoc,←sqrt_mul (by norm_num)]
    have h₁ := sq_sqrt (by norm_num : 0≤(3:ℝ)*6)
    nlinarith [sqrt_nonneg ((3:ℝ)*6)]
  have k2 : (4:ℝ)*sqrt 6 ≤10 := by nlinarith [sq_sqrt (by norm_num : (0:ℝ)≤6),sqrt_nonneg (6:ℝ)]
  have err0 : 4*dy 144000+4*sqrt 3*sqrt 6*R ≤ 22*dy 144000 := by
    calc
      _ ≤ 4*dy 144000+4*sqrt 3*sqrt 6*dy 144000 := by gcongr
      _ ≤ _ := by linarith [mul_le_mul_of_nonneg_right k1 (pos 144000).le]
  have err1 : 4*dy 144000+4*sqrt 6*R ≤14*dy 144000 := by
    calc
      _ ≤ 4*dy 144000+4*sqrt 6*dy 144000 := by gcongr
      _ ≤ _ := by linarith [mul_le_mul_of_nonneg_right k2 (pos 144000).le]
  have hw (n : ℕ) (hn : 1800 ≤ n) : W*dy n ≤ S*dy (n-1800) := calc
    _ ≤ (S/dy 1800)*dy n := mul_le_mul_of_nonneg_right hW' (pos _).le
    _ = _ := by rw [←div n 1800 hn]; ring
  have Ebd : E ≤ S*(4*dy 2100+22*dy 142200) := by
    have A := mul_le_mul_of_nonneg_left err0 hW
    linarith only [hE,A,hM,k0,hw 144000 (by decide)]
  have Eζ : E/dy 1946 ≤ S*(4*dy 154+22*dy 140254) := calc
    _ ≤ S*(4*dy 2100+22*dy 142200)/dy 1946 := div_le_div_of_nonneg_right Ebd (pos _).le
    _ = _ := by rw [←div 2100 1946 (by decide),←div 142200 1946 (by decide)]; ring
  have ed : 16/((2:ℝ)^18000*(dy 4501)^2) = 16*dy 8998 := by
    rw [pow, show (4501:ℕ)*2=9002 from rfl]
    rw [show (2:ℝ)^18000=(dy 18000)⁻¹ from (inv_inv _).symm]
    rw [← div 18000 9002 (by decide)]
    field_simp [ne_of_gt (pos _)]
  have rareScale : dy 146 = dy 144 / 4 := by
    have e := mul 144 2
    change dy 144*dy 2 = dy 146 at e
    rw [←e]; norm_num only [show dy 2=(1/4:ℝ) from by norm_num [dy]]; ring
  have margin : dy 154 = dy 144 / 1024 := by
    have e := mul 144 10
    change dy 144*dy 10=dy 154 at e
    rw [←e]; norm_num only [show dy 10=(1/1024:ℝ) from by norm_num [dy]]; ring
  have tight (n : ℕ) (hn : 154≤n) : S*dy n ≤ S*(dy 144/1024) := by
    rw [←margin]; exact mul_le_mul_of_nonneg_left (antitone hn) hs.le
  have last := mul_le_mul_of_nonneg_left err1 hW
  rw [ed]
  constructor <;>
    linarith only [hM,k0,Eζ,hw 1946 (by decide),hw 4501 (by decide),hw 8998 (by decide),
      hw 144000 (by decide),tight 2100 (by decide),tight 154 (by decide),tight 140254 (by decide),
      tight 7198 (by decide),tight 2701 (by decide),tight 142200 (by decide),last,
      show S*dy 146=S*(dy 144/4) from congrArg (S*·) rareScale]


end
end PlanarUnitDistances.ComparisonConstants
