import PlanarUnitDistances.KPSStationary

/-! Deep Blue. Recover the actual Cartesian equations from the height
hypotheses on the physical edge labels. The torus coordinates are constructed
from these labels, including their fixed rectangle quotients. -/

noncomputable section

namespace PlanarUnitDistances.TorusCritical

open Fibre CriticalLocus GridLocalization

variable {K L I J : Type*} [Field K] [NumberField K] [Field L] [Algebra K L]
  [CharZero L] [IsAlgClosed L] [Fintype I] [Fintype J]

def labelRectangle (c : I → Option J → Kˣ) (i b : I) (j : Option J) :=
  c i j*c b none/(c i none*c b j)

/-- Two distinct column positions on the small side. Each assigned ratio is
the image of its original number-field edge label. The returned scalar and
Cartesian velocities are shared on the whole grid. -/
theorem velocities_with_cap [Nontrivial I]
    (cap : ℝ → ℝ) (hcap : Monotone cap)
    (source : ∀ (S : Finset I) (r : ℕ), StationaryRatioWithCap K L S J r cap)
    (p : I → L × L) (s : Option J → L × L) (c : I → Option J → Kˣ)
    (b : I) (hl : Fintype.card (Option J) ≤ 4) (j₁ j₂ : Option J) (hdist : s j₁ ≠ s j₂)
    (hchord : ∀ i j, let u := algebraMap K L (c i j : K); chordSq (p i) (s j) = 2-u-u⁻¹)
    (scale : ℝ) (hscale : 12*(2:ℝ)^111 ≤ scale) (impossible : ∀ h : ℝ, scale/3 ≤ h → h ≤ cap (24*(scale/(324*2^111))) → False)
    (hlarge : ∀ i j, scale/3 ≤ weilHeight (c i j : K))
    (hrect : ∀ i i' j, weilHeight (labelRectangle c i i' (some j) : K) ≤ scale/(324*2^111)) :
    ∃ (H : I → L × L) (U : Option J → L × L) (A : I → L) (a : Option J → L), ∀ i j,
      A i ≠ a j ∧ 2*dot (p i-s j) (H i-U j) =
        ((algebraMap K L (c i j : K))⁻¹-algebraMap K L (c i j : K))*(A i-a j) := by
  let f := algebraMap K L
  let α (i : I) (j : Option J) := labelRectangle c i b j
  let β := mapUnits f α
  let u := mapUnits f c
  have hα (i : I) : α i none = 1 := by simp [α, labelRectangle, mul_comm]
  have hb (j : Option J) : β b j = 1 := by simp [β,α,mapUnits,labelRectangle,mul_comm]
  have hcol (i : I) : β i none = 1 := by simp [β,mapUnits,hα]
  let t : RatioSolution b none p s β :=
    { ratio := u
      distance := fun i j ↦ by simpa [u,mapUnits,f,Units.val_inv_eq_inv_val] using hchord i j
      rect := fun i j ↦ by
        change _ = (Units.map f.toMonoidHom (labelRectangle c i b j)) * _
        simp only [labelRectangle,map_div,map_mul,u,mapUnits]
        exact (div_mul_cancel _ _).symm }
  let e := torusEquivRatio b none p s β hb hcol
  let sol := e.symm t
  have hval (i j) : chordRatio p s β b sol i j = f (c i j : K) := by
    exact congrArg (fun v : RatioSolution b none p s β ↦ ((v.ratio i j : Lˣ) : L)) (e.apply_symm_apply t)
  have hR (i i' : I) (j : J) : α i (some j)/α i' (some j) = labelRectangle c i i' (some j) := by
    apply Units.ext
    simp only [α,labelRectangle,Units.val_div_eq_div_val,Units.val_mul]
    field_simp
  obtain ⟨v,hv,hm⟩ := jacobian_motion_with_cap cap hcap source α hα p s b sol hl j₁ j₂ hdist
    (fun i j ↦ (c i j : K)) hval scale hscale impossible hlarge
    (fun i i' j ↦ by rw [hR]; exact hrect i i' j)
  let t' := readLocal p s β b sol v
  let B := readShared p s β b sol v
  refine ⟨fun i ↦ (t' i 0,t' i 1),fun j ↦ (B.1 (j,0),B.1 (j,1)),fun i ↦ t' i 2,colLog B,?_⟩
  intro i j
  have hv' : ∀ e, jacobianRow (coordinates p s β b sol) (equation β e) v = 0 := hv
  have hm' : jacobianRow (coordinates p s β b sol) (ratio β i j) v ≠ 0 := hm i j
  rw [← reconstruct_velocity p s β b sol v hv', ratio_velocity] at hm'
  refine ⟨sub_ne_zero.mp (right_ne_zero_of_mul hm'), ?_⟩
  have h := kernel_implies_rowEquation p s β b sol v hv' i j
  change 2*((p i).1-(s j).1)*(t' i 0-B.1 (j,0)) +
    2*((p i).2-(s j).2)*(t' i 1-B.1 (j,1)) = chordRoot p s β b sol i j*(t' i 2-colLog B j) at h
  rw [chordRoot,hval] at h
  simp only [dot, Prod.fst_sub, Prod.snd_sub]
  linear_combination h


end PlanarUnitDistances.TorusCritical
