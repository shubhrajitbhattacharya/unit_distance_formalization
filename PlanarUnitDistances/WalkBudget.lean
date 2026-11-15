import PlanarUnitDistances.GeometricCodegree
import PlanarUnitDistances.CircleSampling
open Filter OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
namespace PlanarUnitDistances
noncomputable section
open scoped Classical
open Finset OAI.PlanarUnitDistances.FiniteInformation

/-- The transition law on the point subtype of the actual finite configuration. -/
noncomputable def unitNeighbors (P : Finset Plane) (q : Plane) : Finset P :=
  Finset.univ.filter fun p : P => dist (p:Plane) q=1

lemma unitNeighbors_card (P : Finset Plane) (q : Plane) :
    ((unitNeighbors P q).card:ℝ) = degree P q := by
  have he : (unitNeighbors P q).map (Function.Embedding.subtype (·∈P)) =
      P.filter (fun p => dist p q=1) := by
    ext p
    simp [unitNeighbors, and_comm]
  unfold degree
  exact_mod_cast (Finset.card_map _).symm.trans (congrArg Finset.card he)

noncomputable def unitCenterLaw (P Q : Finset Plane) (q : Q) : ℝ := degree P q/incidences P Q
noncomputable def unitNeighborLaw (P : Finset Plane) (q : Plane) (p : P) : ℝ :=
  if p ∈ unitNeighbors P q then (degree P q)⁻¹ else 0

/-- Exactly the KL mutual information of the two independent neighbors of one degree-biased center. -/
noncomputable def unitWalkInformation (P Q : Finset Plane) : ℝ :=
  let κ := unitCenterLaw P Q
  let w := fun q : Q => unitNeighborLaw P q
  KL (wedge κ w) (fun z => marginal κ w z.1 * marginal κ w z.2)

theorem unitWalkInformation_bound (P Q : Finset Plane) (hP : P.Nonempty)
    {d : ℝ} (hd : 0<d) (he : 0 < incidences P Q)
    (hD : ∀q ∈ Q,d≤degree P q) (hpos : ∀p ∈ P,0 < degree Q p) :
    unitWalkInformation P Q ≤ 2*Real.log P.card -
      (1-(Q.card:ℝ)/incidences P Q)*Real.log (incidences P Q*d/2) := by
  letI : Nonempty P := hP.to_subtype
  have hsum : (∑q : Q,((unitNeighbors P q).card:ℝ)) = incidences P Q := by
    simp only [unitNeighbors_card,incidences]
    exact Finset.sum_attach Q _
  have hhit (p : P) : ∃q : Q,p∈unitNeighbors P (q:Plane) := by
    have hp := hpos p p.2
    unfold degree at hp
    obtain ⟨q,hq⟩ := Finset.card_pos.mp (Nat.cast_pos.mp hp)
    obtain ⟨hq,hd⟩ := Finset.mem_filter.mp hq
    exact ⟨⟨q,hq⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(dist_comm ..).trans hd⟩⟩
  have h := euclidean_unit_graph_mutual_information ((↑) : P → Plane) ((↑) : Q → Plane)
    Subtype.val_injective Subtype.val_injective (fun q => unitNeighbors P q)
    (fun _ _ h => (Finset.mem_filter.mp h).2) hd
    (fun q => by rw [unitNeighbors_card]; exact hD q q.2) he hsum hhit
  unfold unitWalkInformation unitCenterLaw unitNeighborLaw
  simpa only [unitNeighbors_card,Fintype.card_coe] using h

/-- The marginal of the explicit two-stage law is the uniform-edge degree marginal. -/
theorem unitWalk_marginal_eq_degree (P Q : Finset Plane) (p : P) :
    marginal (unitCenterLaw P Q) (fun q : Q => unitNeighborLaw P q) p =
      degree Q p/incidences P Q := by
  unfold marginal
  have hterm (q : Q) : unitCenterLaw P Q q * unitNeighborLaw P q p =
      (if dist (p:Plane) (q:Plane)=1 then (1:ℝ) else 0)/incidences P Q := by
    by_cases h : dist (p:Plane) (q:Plane)=1
    · have hm : p ∈ unitNeighbors P q := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
      have hd := (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨p,hm⟩) :
        0 < ((unitNeighbors P q).card:ℝ))
      rw [unitNeighbors_card] at hd
      simp only [unitCenterLaw,unitNeighborLaw,if_pos hm,if_pos h,div_eq_mul_inv]
      field_simp [hd.ne']
    · have hm : p ∉ unitNeighbors P q := fun hp => h (Finset.mem_filter.mp hp).2
      simp [unitNeighborLaw,hm,h]
  simp only [hterm,← Finset.sum_div,degree_sum]
  congr 1
  rw [show (Finset.univ : Finset Q) = Q.attach by ext; simp]
  simpa only [dist_comm (p:Plane)] using
    Finset.sum_attach Q (fun q => if dist (p:Plane) q=1 then (1:ℝ) else 0)

/-- Fixed-exponent information budget with the exact diagonal correction retained. -/
theorem fixed_information_bound {g : ℝ} (hg : 0<g) (ha1 : 10000*g ≤ 1/10) :
    let a := 10000*g
    ∀ᶠ t : ℝ in atTop, ∀ {m n e D : ℝ}, 0 < m → 0 ≤ n →
      m≤2*t^(1+2*a) → n≤t^(2+a) → t^(2+2*a-90*g)≤e →
      D ≤ 2*Real.log m-(1-n/e)*Real.log (e*((27/50:ℝ)*t^(a-90*g))/2) →
      D+1 ≤ 10200*g*Real.log t := by
  let a := 10000*g
  let v := 2+3*a-180*g
  let c : ℝ := 27/100
  have hv : 0<v := by dsimp [v,a]; linarith
  have hv3 : v≤3 := by dsimp [v,a]; linarith
  have hc : 0<c := by norm_num [c]
  have hneg : -(a-90*g)<0 := by dsimp [a]; linarith
  have hdiag := (tendsto_rpow_neg_atTop (neg_pos.mpr hneg)).eventually_le_const
    (show (0:ℝ)<g by exact hg)
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop ((2*Real.log 2-Real.log c+1)/(17*g))
  have hK := (tendsto_rpow_atTop hv).eventually_ge_atTop c⁻¹
  filter_upwards [hdiag,hlog,hK,eventually_ge_atTop (1:ℝ)] with t hdiag hlog hK ht
  have ht0 := zero_lt_one.trans_le ht
  have hlog0 := Real.log_nonneg ht
  have hd := Real.rpow_pos_of_pos ht0 (a-90*g)
  intro m n e D hm hn hm' hn' he hD
  have he0 := (Real.rpow_pos_of_pos ht0 _).trans_le he
  have hoff := div_le_div₀ (Real.rpow_nonneg ht0.le _) hn' (Real.rpow_pos_of_pos ht0 _) he
  rw [←Real.rpow_sub ht0] at hoff
  have hx : 2+a-(2+2*a-90*g) = -(a-90*g) := by ring
  have hdiag' : t^(-(a-90*g))≤g := by simpa only [neg_neg] using hdiag
  change t^(2+2*a-90*g)≤e at he
  change n≤t^(2+a) at hn'
  change n/e≤t^(2+a-(2+2*a-90*g)) at hoff
  rw [hx] at hoff
  have hprob := hoff.trans hdiag'
  have hprob1 : n/e≤1 := by dsimp [a] at *; linarith
  have hprob0 := div_nonneg hn he0.le
  have hlm := Real.log_le_log hm hm'
  rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos ht0 _).ne',Real.log_rpow ht0] at hlm
  have hscale : c*t^v ≤ e*((27/50:ℝ)*t^(a-90*g))/2 := by
    have hh := mul_le_mul_of_nonneg_right he hd.le
    rw [←Real.rpow_add ht0] at hh
    have hvv : 2+2*a-90*g+(a-90*g)=v := by dsimp [v]; ring
    rw [hvv] at hh
    dsimp [c]; linarith
  have hclog := Real.log_le_log (mul_pos hc (Real.rpow_pos_of_pos ht0 _)) hscale
  rw [Real.log_mul hc.ne' (Real.rpow_pos_of_pos ht0 _).ne',Real.log_rpow ht0] at hclog
  have hcl0 : 0 ≤ Real.log c + v*Real.log t := by
    rw [←Real.log_rpow ht0,←Real.log_mul hc.ne' (Real.rpow_pos_of_pos ht0 _).ne']
    apply Real.log_nonneg
    have h := mul_le_mul_of_nonneg_left hK hc.le
    rwa [mul_inv_cancel₀ hc.ne'] at h
  have hclUpper : Real.log c+v*Real.log t ≤ 3*Real.log t := by
    have hc1 : c≤1 := by norm_num [c]
    linarith [Real.log_nonpos hc.le hc1,mul_le_mul_of_nonneg_right hv3 hlog0]
  have hcorr := mul_le_mul hprob hclUpper hcl0 hg.le
  have hcst := (div_le_iff₀ (show 0<17*g by linarith)).mp hlog
  have hretain := mul_le_mul_of_nonneg_left hclog (sub_nonneg.mpr hprob1)
  change D ≤ 2*Real.log m-(1-n/e)*Real.log (e*((27/50:ℝ)*t^(a-90*g))/2) at hD
  change Real.log m≤Real.log 2+(1+2*a)*Real.log t at hlm
  dsimp [v,a] at hcorr hretain hlm
  nlinarith only [hD,hretain,hlm,hcorr,hcst]

end
end PlanarUnitDistances
