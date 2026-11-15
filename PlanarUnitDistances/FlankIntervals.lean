import Mathlib
open MeasureTheory Set Filter
namespace PlanarUnitDistances.Flanks
noncomputable section
open scoped Classical

/-- Lebesgue length of the intersection of two closed intervals. -/
def overlap (a b l r : ℝ) := max 0 (min b r-max a l)

private lemma overlap_le (a b l r : ℝ) (hab : a≤b) : overlap a b l r ≤ b-a :=
  max_le (sub_nonneg.mpr hab) (sub_le_sub (min_le_left ..) (le_max_left ..))

lemma overlap_budget {b b' T l r ℓ : ℝ} (hbb : b≤b') (hT : 0≤T) (hℓ : 0≤ℓ) :
    (1-ℓ)*(2*T)+2*ℓ*(overlap (b-T) b l r+overlap b' (b'+T) l r)
      ≤ 2*T+ℓ*(if b ∈ Ioo l r ∧ b' ∈ Ioo l r then max 0 (r-l) else 0) := by
  let A := overlap (b-T) b l r
  let B := overlap b' (b'+T) l r
  have hA : A≤T := (overlap_le _ _ _ _ (by linarith : b-T≤b)).trans_eq (by ring)
  have hB : B≤T := (overlap_le _ _ _ _ (by linarith : b'≤b'+T)).trans_eq (by ring)
  change (1-ℓ)*(2*T)+2*ℓ*(A+B) ≤ _
  by_cases hsum : A+B≤T
  · have hnm : 0≤ℓ*(if b∈Ioo l r ∧ b'∈Ioo l r then max 0 (r-l) else 0) := by
      split_ifs <;> positivity
    nlinarith [mul_le_mul_of_nonneg_left hsum hℓ]
  have hap : 0<A := by linarith
  have hbp : 0<B := by linarith
  have ha : 0 < min b r-max (b-T) l := (lt_max_iff.mp hap).resolve_left (lt_irrefl 0)
  have hb : 0 < min (b'+T) r-max b' l := (lt_max_iff.mp hbp).resolve_left (lt_irrefl 0)
  have hlo : l<b := by linarith [le_max_right (b-T) l,min_le_left b r]
  have hhi : b'<r := by linarith [le_max_left b' l,min_le_right (b'+T) r]
  have hboth : b ∈ Ioo l r ∧ b' ∈ Ioo l r := ⟨⟨hlo,hbb.trans_lt hhi⟩,⟨hlo.trans_le hbb,hhi⟩⟩
  rw [if_pos hboth,max_eq_right (by linarith : 0≤r-l)]
  have hAB : A+B≤r-l := by
    dsimp only [A,B,overlap]
    rw [max_eq_right ha.le,max_eq_right hb.le]
    linarith [le_max_right (b-T) l,min_le_left b r,le_max_left b' l,min_le_right (b'+T) r]
  have hgain : 2*(A+B-T)≤r-l := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hgain hℓ]

/-- Integral of a constant times the indicator of one bounded interval. -/
private lemma interval_integral (a b x : ℝ) :
    (∫ s : ℝ,(Icc a b).indicator (fun _ => x) s)=max 0 (b-a)*x := by
  rw [integral_indicator_const x measurableSet_Icc,Real.volume_real_Icc]
  simp only [smul_eq_mul,max_comm]

private lemma interval_integrable (a b x : ℝ) :
    Integrable ((Icc a b).indicator (fun _ : ℝ => x)) :=
  ((continuous_const : Continuous (fun _ : ℝ => x)).integrableOn_Icc).integrable_indicator measurableSet_Icc

/-- The common-level upper envelope on one flank: the overlap with the balanced
window carries the excess coefficient 2ℓ. -/
def flankDensity (a b l r ℓ s : ℝ) :=
  (Icc a b).indicator (fun _ => 1-ℓ) s +
    (Icc (max a l) (min b r)).indicator (fun _ => 2*ℓ) s

lemma flankDensity_integral (a b l r ℓ : ℝ) :
    (∫s,flankDensity a b l r ℓ s)=max 0 (b-a)*(1-ℓ)+overlap a b l r*(2*ℓ) := by
  unfold flankDensity
  rw [integral_add (interval_integrable ..) (interval_integrable ..),
    interval_integral,interval_integral]
  rfl

lemma integrated_common_flanks {b b' T l r ℓ : ℝ}
    (hbb : b≤b') (hT : 0≤T) (hℓ : 0≤ℓ) :
    (∫s,flankDensity (b-T) b l r ℓ s+flankDensity b' (b'+T) l r ℓ s) ≤
      2*T+ℓ*(if b ∈ Ioo l r ∧ b' ∈ Ioo l r then max 0 (r-l) else 0) := by
  have hf (x y : ℝ) : Integrable (flankDensity x y l r ℓ) :=
    (interval_integrable ..).add (interval_integrable ..)
  rw [integral_add (hf ..) (hf ..), flankDensity_integral,flankDensity_integral,
    show b-(b-T)=T by ring,show b'+T-b'=T by ring,max_eq_right hT]
  linarith [overlap_budget (l:=l) (r:=r) hbb hT hℓ]


/-- The two density coefficients can be read directly from membership in the
flank and in the window. Its boundary conventions are immaterial to integration. -/
lemma flankDensity_eq (a b l r ℓ s : ℝ) :
    flankDensity a b l r ℓ s =
      if s∈Icc a b then (if s∈Icc l r then 1+ℓ else 1-ℓ) else 0 := by
  have hi : s∈Icc (max a l) (min b r) ↔ s∈Icc a b ∧ s∈Icc l r := by
    simp only [mem_Icc,max_le_iff,le_min_iff]; tauto
  unfold flankDensity
  by_cases h : s∈Icc a b <;> by_cases j : s∈Icc l r <;>
    (simp [hi,h,j]; try ring)

/-- A rare occurrence of either orientation fixes the only remaining flank;
the other flank is too late (respectively too early) by monotonicity of the
global bit-one frequency. The common-only case uses the exact overlap bound. -/
theorem antitone_level_budget {b b' T l r ε ℓ : ℝ} {f : ℝ → ℝ} (hf : Antitone f)
    (hbb : b≤b') (hT : 0≤T) (hε : ε≤1/2) (hℓ : 0≤ℓ) (hℓ1 : ℓ≤1)
    (one zero : ℝ → Prop) (common : ℝ → ℝ)
    (h1 : ∀s,one s → s∈Icc (b-T) b ∧ f s<ε)
    (h0 : ∀s,zero s → s∈Icc b' (b'+T) ∧ 1-ε<f s)
    (hc : ∀s,common s≠0 → ε≤f s ∧ f s≤1-ε ∧
      (s∈Icc (b-T) b ∨ s∈Icc b' (b'+T)) ∧
      common s≤(if s∈Icc l r then 1+ℓ else 1-ℓ))
    (hInt : Integrable (fun s => (if one s ∨ zero s then (2:ℝ) else 0)+common s)) :
    (∫s, (if one s ∨ zero s then (2:ℝ) else 0)+common s) ≤
      2*T+ℓ*(if b∈Ioo l r ∧ b'∈Ioo l r then max 0 (r-l) else 0) := by
  classical
  let g := fun s => (if one s ∨ zero s then (2:ℝ) else 0)+common s
  have hbound (s : ℝ) : g s≤2 := by
    by_cases hr : one s ∨ zero s
    · have z : common s=0 := by
        by_contra hh
        obtain ⟨hlo,hhi,_⟩ := hc s hh
        rcases hr with h | h
        · linarith [(h1 s h).2]
        · linarith [(h0 s h).2]
      simp [g,hr,z]
    · simp only [g,if_neg hr,zero_add]
      by_cases hz : common s=0
      · simp [hz]
      · have h := (hc s hz).2.2.2; split_ifs at h <;> linarith
  have hCap : 2*T ≤ 2*T+ℓ*(if b∈Ioo l r ∧ b'∈Ioo l r then max 0 (r-l) else 0) := by
    apply le_add_of_nonneg_right; split_ifs <;> positivity
  have hSingle (x y : ℝ) (hxy : y-x=T) (hs : ∀s,s∉Icc x y → g s=0) :
      (∫s,g s)≤2*T := by
    have hh := integral_mono hInt (interval_integrable x y 2) (fun s => show g s≤_ from by
      by_cases h : s∈Icc x y
      · simpa only [indicator_of_mem h] using hbound s
      · simp [indicator_of_notMem h,hs s h])
    rw [interval_integral,hxy,max_eq_right hT] at hh
    linarith
  change (∫s,g s)≤_
  by_cases hOne : ∃s,one s
  · obtain ⟨s₀,hs₀⟩ := hOne
    obtain ⟨hsL,hfs⟩ := h1 s₀ hs₀
    apply le_trans (hSingle (b-T) b (by ring) ?_) hCap
    intro s hs
    have hn1 : ¬one s := fun h => hs (h1 s h).1
    have hn0 : ¬zero s := by
      intro h
      have he := hf (hsL.2.trans (hbb.trans (h0 s h).1.1))
      linarith [(h0 s h).2]
    have hnC : common s=0 := by
      by_contra h
      obtain ⟨hl,_,hS,_⟩ := hc s h
      have hR := hS.resolve_left hs
      linarith [hf (hsL.2.trans (hbb.trans hR.1))]
    simp [g,hn1,hn0,hnC]
  · have hn1 : ∀s,¬one s := fun s h => hOne ⟨s,h⟩
    by_cases hZero : ∃s,zero s
    · obtain ⟨s₀,hs₀⟩ := hZero
      obtain ⟨hsR,hfs⟩ := h0 s₀ hs₀
      apply le_trans (hSingle b' (b'+T) (by ring) ?_) hCap
      intro s hs
      have hn0 : ¬zero s := fun h => hs (h0 s h).1
      have hnC : common s=0 := by
        by_contra h
        obtain ⟨_,hu,hS,_⟩ := hc s h
        have hL := hS.resolve_right hs
        linarith [hf (hL.2.trans (hbb.trans hsR.1))]
      simp [g,hn1,hn0,hnC]
    · have hn0 : ∀s,¬zero s := fun s h => hZero ⟨s,h⟩
      have hfi (x y : ℝ) : Integrable (flankDensity x y l r ℓ) :=
        (interval_integrable ..).add (interval_integrable ..)
      apply le_trans _ (integrated_common_flanks hbb hT hℓ)
      apply integral_mono hInt ((hfi ..).add (hfi ..))
      intro s
      simp only [if_neg (not_or.mpr ⟨hn1 s,hn0 s⟩),zero_add,Pi.add_apply,flankDensity_eq]
      by_cases hh : common s=0
      · rw [hh]; split_ifs <;> linarith
      · obtain ⟨_,_,hs,hg⟩ := hc s hh
        split_ifs at hg ⊢ <;> simp_all <;> linarith

end
end PlanarUnitDistances.Flanks
