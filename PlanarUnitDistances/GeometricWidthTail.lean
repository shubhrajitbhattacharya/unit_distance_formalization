import PlanarUnitDistances.TailUniformEdge
import PlanarUnitDistances.RareLabels

namespace PlanarUnitDistances.Competition.IncidencePiece
open Real Finset
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

private theorem epsilon_power : eps^(1/25:ℝ)=1/(2:ℝ)^72 := by
  unfold eps
  rw [←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  norm_num [Real.rpow_neg]

private theorem cutoff_coefficient {f g ξ m : ℝ} (hf : 0≤f) (hg : 0≤g)
    (hsf : f≤2*eps) (hsg : g≤1/2) (hxi : ξ≤1/(2:ℝ)^72)
    (cut : m≤2*f^(27/50:ℝ)*g^(27/50:ℝ)+2*ξ*sqrt (f*g)) :
    m ≤ (4/(2:ℝ)^72)*sqrt (f*g) := by
  have ep : 0≤eps := by unfold eps; positivity
  have fg : f*g≤eps := (mul_le_mul hsf hsg hg (by positivity)).trans_eq (by ring)
  have a := (Real.rpow_le_rpow (mul_nonneg hf hg) fg (by norm_num : (0:ℝ)≤1/25)).trans_eq epsilon_power
  have pow : f^(27/50:ℝ)*g^(27/50:ℝ) = sqrt (f*g)*(f*g)^(1/25:ℝ) := by
    rw [←Real.mul_rpow hf hg,Real.sqrt_eq_rpow,←Real.rpow_add_of_nonneg (mul_nonneg hf hg) (by norm_num) (by norm_num)]
    norm_num
  apply cut.trans
  calc
    _ = (2*(f*g)^(1/25:ℝ)+2*ξ)*sqrt (f*g) := by
      rw [mul_assoc 2,pow]; ring
    _ ≤ (4/(2:ℝ)^72)*sqrt (f*g) := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      linarith

set_option maxHeartbeats 800000 in
/-- The rare upper-tail bound on the literal edge and triple experiments.
The pointwise premise is required only on pairs of distinct actual
neighbors. The large integrated widths, local inconsistency and pointwise
inequality are the three arithmetic inputs to the geometric truncation. -/
theorem geometric_width_tail (M : IncidencePiece K) {t S : ℝ} (reg : Regular M t)
    (ht : 0<t) (hS : 0<S) (hlarge : 192≤S/(2:ℝ)^144)
    (hξ : t^(-150*savingG)≤1/(2:ℝ)^72)
    (hdeg : ∀p∈M.P, 2≤M.degreeP p)
    (X Y : Plane → ℝ) (m : Plane×Plane → ℝ)
    (hX0 : ∀e∈M.E,0≤X e.1) (hY0 : ∀e∈M.E,0≤Y e.2) (hm0 : ∀e∈M.E,0≤m e)
    (hX : M.edgeMean (fun e => X e.1)≤4*S)
    (hY : M.edgeMean (fun e => Y e.2)≤4*S) (hm : M.edgeMean m≤4)
    (hpair : ∀p∈M.P, ∀q r : Plane, (p,q)∈M.E → (p,r)∈M.E → q≠r →
      2*X p≤3*(Y q+m (p,q)+(Y r+m (p,r)))+2*S/eps) :
    M.edgeMean (fun e => max (X e.1-2*S/eps) 0) ≤ (2:ℝ)^12/2^144*S ∧
    (∑v : Triple M,M.mass v*(if 8*S/eps<X v.1.val+X v.2.2.val then X v.1.val+X v.2.2.val else 0))
      ≤ (2:ℝ)^14/2^144*S := by
  let B := 2*S/eps
  let α := 4/(2:ℝ)^72
  have ep : 0<eps := by unfold eps; positivity
  have esmall : eps≤1/48 := by
    unfold eps
    apply le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (by norm_num : -(1800:ℝ)≤ -6))
    norm_num
  have hB : 0<B := div_pos (by positivity) ep
  have cut (u : ℝ) (hu : B≤u) :
      M.edgeProb (fun e => u<X e.1 ∧ u/12≤Y e.2) ≤
        α*sqrt (M.edgeProb (fun e => u<X e.1)*M.edgeProb (fun e => u/12≤Y e.2)) := by
    have x := (M.edge_markov (fun e => X e.1) hX0 (hB.trans_le hu).le (fun e => u<X e.1)
      (fun _ _ h => h.le)).trans hX
    have y := (M.edge_markov (fun e => Y e.2) hY0 (div_nonneg (hB.trans_le hu).le (by norm_num))
      (fun e => u/12≤Y e.2) (fun _ _ h => h)).trans hY
    have fx : 0≤M.edgeProb (fun e => u<X e.1) := by unfold edgeProb; positivity
    have fy : 0≤M.edgeProb (fun e => u/12≤Y e.2) := by unfold edgeProb; positivity
    have Bmul := (mul_le_mul_of_nonneg_right hu fx).trans x
    have Cmul := (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hu (by norm_num : (0:ℝ)≤12)) fy).trans y
    have Bx : M.edgeProb (fun e => u<X e.1)≤2*eps := by
      let z := M.edgeProb (fun e => u<X e.1)
      change z≤2*eps
      apply (le_of_mul_le_mul_left ?_ hS)
      calc
        S*z = B*z*(eps/2) := by dsimp only [B]; field_simp <;> ring
        _ ≤ 4*S*(eps/2) := mul_le_mul_of_nonneg_right Bmul (by positivity)
        _ = S*(2*eps) := by ring
    have Cy : M.edgeProb (fun e => u/12≤Y e.2)≤1/2 := by
      let z := M.edgeProb (fun e => u/12≤Y e.2)
      have v : z≤24*eps := by
        apply (le_of_mul_le_mul_left ?_ hS)
        calc
          S*z = B/12*z*(6*eps) := by dsimp only [B]; field_simp <;> ring
          _ ≤ 4*S*(6*eps) := mul_le_mul_of_nonneg_right Cmul (by positivity)
          _ = S*(24*eps) := by ring
      change z≤1/2
      linarith only [v,esmall]
    exact cutoff_coefficient fx fy Bx Cy hξ
      (M.edgeProb_rectangle_marginals reg ht (fun p => u<X p) (fun q => u/12≤Y q))
  have event (u : ℝ) (hu : B≤u) := cut u hu
  have res := edge_width_tail (P := ↥M.P) (fun p : M.P => ↥(M.centerFiber p)) (fun _ => 1/(M.E.card:ℝ)) (fun p => X p.val)
    (fun _ q => Y q.val) (fun p q => m (p.val,q.val)) (α:=α) (S:=S) (B₀:=B) hS hB.le
    (fun _ => by positivity) (fun _ q => hY0 _ (mem_filter.mp q.prop).2)
    (fun _ q => hm0 _ (mem_filter.mp q.prop).2)
    (fun p => by rw [Fintype.card_coe]; exact hdeg p p.prop)
    (fun p q r qr => hpair p p.prop q r (mem_filter.mp q.prop).2 (mem_filter.mp r.prop).2 (Subtype.val_injective.ne qr))
    (fun u hu => by simpa only [←M.fiber_event] using event u hu)
    (by norm_num [α]) (by exact (M.fiber_mean (fun e => Y e.2)).trans_le hY)
    (by exact (M.fiber_mean m).trans_le hm) hlarge
  have point : M.edgeMean (fun e => max (X e.1-B) 0) ≤ (2:ℝ)^12/2^144*S :=
    (M.fiber_mean (fun e => max (X e.1-B) 0)).symm.trans_le res
  have lm := M.leg_means (fun p => max (X p-B) 0)
  have pairs := truncated_pair_width M.mass (fun v => X v.1.val) (fun v => X v.2.2.val)
    (B₀:=B) M.mass_nonnegative (lm.1.trans_le point) (lm.2.trans_le point)
  refine ⟨point,?_⟩
  dsimp [B] at pairs
  rw [show (4:ℝ)*(2*S/eps)=8*S/eps by ring] at pairs
  exact pairs.trans_eq (by ring)

end
end PlanarUnitDistances.Competition.IncidencePiece

