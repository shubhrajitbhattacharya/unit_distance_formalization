import PlanarUnitDistances.Rare
import PlanarUnitDistances.TripleLaw

namespace PlanarUnitDistances.Competition.IncidencePiece
open Finset Real Set
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

private def fiber (M : IncidencePiece K) (F : Finset Plane) (q : Plane) : ℝ :=
  ((F.filter (fun p => (p,q)∈M.E)).card:ℝ)

private lemma cut_fiber (M : IncidencePiece K) (F B : Finset Plane) :
    ∑ q∈B,fiber M F q=((M.E∩(F×ˢB)).card:ℝ) := by
  have eq : M.E∩(F×ˢB)=(F×ˢB).filter (fun e => e∈M.E) := by
    ext e; simp [and_comm]
  rw [eq,natCast_card_filter,sum_product_right]
  simp only [fiber,natCast_card_filter]

private lemma cut_all (M : IncidencePiece K) (F : Finset Plane) :
    ((M.E∩(F×ˢM.Q)).card:ℝ)/M.E.card=∑p∈F,M.mu p := by
  have eq : M.E∩(F×ˢM.Q)=(F×ˢM.Q).filter (fun e => e∈M.E) := by
    ext e; simp [and_comm]
  simp only [mu,degreeP,←sum_div,eq,natCast_card_filter,sum_product]

private lemma marginal_cut {u v h k x m : ℝ} (hu : 0≤u) (hv : 0≤v) (hx : 0≤x)
    (hp : (27/50:ℝ)*u≤h) (hq : (27/50:ℝ)*v≤k)
    (cut : m≤sqrt (u*v)*((u*v)^(1/25:ℝ)+x)) :
    m≤2*h^(27/50:ℝ)*k^(27/50:ℝ)+2*x*sqrt (h*k) := by
  let g : ℝ := 27/50
  have gp : 0<g := by norm_num [g]
  have hh : 0≤h := (mul_nonneg gp.le hu).trans hp
  have hk : 0≤k := (mul_nonneg gp.le hv).trans hq
  have uv := mul_nonneg hu hv
  have hk' := mul_nonneg hh hk
  have hhq : (g*g)*(u*v)≤h*k := by
    calc
      _ = (g*u)*(g*v) := by ring
      _ ≤ _ := mul_le_mul hp hq (mul_nonneg gp.le hv) hh
  have root := Real.sqrt_le_sqrt hhq
  rw [Real.sqrt_mul (mul_nonneg gp.le gp.le),Real.sqrt_mul_self gp.le] at root
  have b : sqrt (u*v) ≤ g⁻¹*sqrt (h*k) := by
    rw [←div_eq_inv_mul]; exact (le_div_iff₀ gp).2 (by rwa [mul_comm])
  have pow_id (a : ℝ) (ha : 0≤a) : (sqrt a)^(2/25:ℝ)=a^(1/25:ℝ) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul ha]; norm_num
  have bb := Real.rpow_le_rpow (Real.sqrt_nonneg _) b (by norm_num : (0:ℝ)≤2/25)
  rw [Real.mul_rpow (inv_nonneg.mpr gp.le) (Real.sqrt_nonneg _),pow_id _ hk',pow_id _ uv] at bb
  have cg : g⁻¹*(g⁻¹)^(2/25:ℝ)=g^(-(1+2/25):ℝ) := by
    rw [Real.inv_rpow gp.le,Real.rpow_neg gp.le,Real.rpow_add gp]
    rw [Real.rpow_one,mul_inv]
  apply rare_rectangle_power hh hk hx rare_marginal_constants.1 rare_marginal_constants.2
  apply cut.trans
  calc
    _ ≤ (g⁻¹*sqrt (h*k))*((g⁻¹)^(2/25:ℝ)*(h*k)^(1/25:ℝ)+x) :=
      mul_le_mul b (add_le_add bb le_rfl) (add_nonneg (Real.rpow_nonneg uv _) hx)
        (mul_nonneg (inv_nonneg.mpr gp.le) (Real.sqrt_nonneg _))
    _ = _ := by rw [←cg]; ring

private lemma marginal_sum (F : Finset Plane) (n : ℕ) (w : Plane → ℝ)
    (h : ∀p∈F,gamma/n≤w p) : gamma*((F.card:ℝ)/n) ≤ ∑p∈F,w p := by
  calc
    _ = ∑_p∈F,gamma/n := by simp [nsmul_eq_mul]; ring
    _ ≤ _ := sum_le_sum h

private lemma triple_fiber (M : IncidencePiece K) (F : Finset Plane) (hF : F⊆M.P)
    (he : (M.E.card:ℝ)≠0) (hd : ∀q : M.Q,(M.degreeQ q.val:ℝ)≠0) :
    (∑ v : Triple M, if v.1.val∈F ∧ v.2.2.val∈F then M.mass v else 0)=
      ∑q : M.Q,M.kappa q.val*(fiber M F q.val/M.degreeQ q.val)^2 := by
  let bit (p : M.P) (q : M.Q) : ℝ := if p.val∈F ∧ (p.val,q.val)∈M.E then 1 else 0
  have bs (q : M.Q) : ∑p,bit p q=fiber M F q.val := by
    have eq : (M.P.filter (fun p=>p∈F ∧ (p,q.val)∈M.E))=F.filter (fun p=>(p,q.val)∈M.E) := by
      ext p; simp only [mem_filter]; exact ⟨And.right,fun h => ⟨hF h.1,h⟩⟩
    rw [show (∑p,bit p q)=∑p∈M.P,if p∈F ∧ (p,q.val)∈M.E then (1:ℝ) else 0
      from sum_coe_sort M.P (fun p => if p∈F ∧ (p,q.val)∈M.E then (1:ℝ) else 0),
      ←natCast_card_filter,eq]; rfl
  have one (p r : M.P) (q : M.Q) :
      (if p.val∈F ∧ r.val∈F then M.mass (p,q,r) else 0)=
      bit p q*bit r q/((M.E.card:ℝ)*M.degreeQ q.val) := by
    by_cases hp : p.val∈F <;> by_cases hr : r.val∈F <;>
      by_cases h1 : (p.val,q.val)∈M.E <;> by_cases h2 : (r.val,q.val)∈M.E <;>
      simp [mass,bit,hp,hr,h1,h2]
  simp only [Fintype.sum_prod_type,one]
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  simp_rw [←sum_div,←mul_sum,bs,←sum_mul,bs]
  unfold kappa
  field_simp [he,hd q]

/-- Manuscript Lemma cb:rare on the original weighted common-center walk.
The point set F, both marginals, every rectangle and both sampled endpoints
are measured on the same regular piece; repeated endpoints are included. -/
theorem rare_walk (M : IncidencePiece K) {t δ : ℝ} (reg : Regular M t) (ht : 0<t)
    (hξ : t^(-150*savingG)≤1) (F : Finset Plane) (hF : F⊆M.P)
    (hδ : (∑p∈F,M.mu p)≤δ) (hδ1 : δ≤1) :
    (∑v : Triple M, if v.1.val∈F ∧ v.2.2.val∈F then M.mass v else 0) ≤
      256*(∑p∈F,M.mu p)*max (δ^(4/27:ℝ)) (t^(-150*savingG)) := by
  let f (q : M.Q) := fiber M F q.val/M.degreeQ q.val
  let κ (q : M.Q) := M.kappa q.val
  have he : (0:ℝ)<M.E.card := (Real.rpow_pos_of_pos ht _).trans_le reg.size
  have hd (q : M.Q) : (0:ℝ)<M.degreeQ q.val :=
    (mul_pos (show 0<gamma by norm_num [gamma]) (Real.rpow_pos_of_pos ht _)).trans_le
      (reg.center_degree q q.prop).1
  have hf (q : M.Q) : f q∈Icc (0:ℝ) 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) (hd q).le,(div_le_one (hd q)).2 ?_⟩
    unfold fiber degreeQ
    exact_mod_cast Finset.card_le_card (filter_subset_filter (fun p => (p,q.val)∈M.E) hF)
  have weighted (q : M.Q) : κ q*f q=fiber M F q.val/M.E.card := by
    dsimp only [κ,f,kappa]
    field_simp [he.ne',(hd q).ne']
  have mean : (∑q,κ q*f q)=∑p∈F,M.mu p := by
    simp_rw [weighted]
    rw [sum_coe_sort M.Q (fun q => fiber M F q/M.E.card),←sum_div,cut_fiber,cut_all]
  rw [triple_fiber M F hF he.ne' (fun q => (hd q).ne')]
  apply rare_two_neighbors κ f _ δ (t^(-150*savingG)) (fun q => div_nonneg (hd q).le he.le) hf
    mean hδ hδ1 (Real.rpow_nonneg ht.le _) hξ
  intro G
  let B := G.map (Function.Embedding.subtype (·∈M.Q))
  have hB : B⊆M.Q := by intro q hq; obtain ⟨r,_,rfl⟩ := mem_map.mp hq; exact r.prop
  have cut : (∑q∈G,κ q*f q)=((M.E∩(F×ˢB)).card:ℝ)/M.E.card := by
    simp_rw [weighted]
    rw [←sum_div,←cut_fiber]
    simp only [B,sum_map,Function.Embedding.subtype_apply]
  have ksum : (∑q∈G,κ q)=∑q∈B,M.kappa q := by simp [B,κ]
  rw [cut,ksum]
  apply marginal_cut (by positivity) (by positivity) (Real.rpow_nonneg ht.le _)
    (marginal_sum F _ M.mu (fun p hp => (reg.point_marginal p (hF hp)).1))
    (marginal_sum B _ M.kappa (fun q hq => reg.center_marginal q (hB hq)))
  exact reg.rectangle F B hF hB

open MeasureTheory

/-- Integrated coincidence on the same physical walk. A measurable,
finite-range selection of exceptional points may depend on the level.
The level measure can include the normalized weights of all places. -/
theorem integrated_rare_walk {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν]
    (M : IncidencePiece K) {t δ S : ℝ} (reg : Regular M t) (ht : 0<t)
    (hξ : t^(-150*savingG)≤1) (F : SimpleFunc Ω (Finset Plane)) (hF : ∀s,F s⊆M.P)
    (hδ : ∀s,(∑p∈F s,M.mu p)≤δ) (hδ1 : δ≤1) (hδ0 : 0≤δ)
    (hw : (∫s,∑p∈F s,M.mu p ∂ν)≤4*S) :
    (∫s,∑v : Triple M, if v.1.val∈F s ∧ v.2.2.val∈F s then M.mass v else 0 ∂ν) ≤
      1024*max (δ^(4/27:ℝ)) (t^(-150*savingG))*S := by
  let J (A : Finset Plane) := ∑v : Triple M, if v.1.val∈A ∧ v.2.2.val∈A then M.mass v else 0
  let H (A : Finset Plane) := ∑p∈A,M.mu p
  let c := 256*max (δ^(4/27:ℝ)) (t^(-150*savingG))
  have intJ : Integrable (fun s => J (F s)) ν := (F.map J).integrable_of_isFiniteMeasure
  have intH : Integrable (fun s => H (F s)) ν := (F.map H).integrable_of_isFiniteMeasure
  have hi := integral_mono intJ (intH.const_mul c) (fun s => (rare_walk M reg ht hξ (F s)
    (hF s) (hδ s) hδ1).trans_eq (by dsimp [H,c]; ring))
  rw [integral_const_mul] at hi
  have hc : 0≤c := mul_nonneg (by norm_num) ((Real.rpow_nonneg hδ0 _).trans (le_max_left ..))
  exact hi.trans ((mul_le_mul_of_nonneg_left hw hc).trans_eq (by dsimp only [c]; ring))

/-- With the actual rare cutoff 4ε the integrated coincidence is at most
2⁻¹⁴⁴ S. Even the weaker graph error 2⁻¹⁵⁴ suffices. -/
theorem rare_walk_budget {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν]
    (M : IncidencePiece K) {t S : ℝ} (reg : Regular M t) (ht : 0<t) (hS : 0≤S)
    (hξ : t^(-150*savingG)≤(2:ℝ)^(-154:ℝ))
    (F : SimpleFunc Ω (Finset Plane)) (hF : ∀s,F s⊆M.P)
    (hδ : ∀s,(∑p∈F s,M.mu p)≤4*eps)
    (hw : (∫s,∑p∈F s,M.mu p ∂ν)≤4*S) :
    (∫s,∑v : Triple M, if v.1.val∈F s ∧ v.2.2.val∈F s then M.mass v else 0 ∂ν)
      ≤ (2:ℝ)^(-144:ℝ)*S := by
  have small (n : ℝ) (hn : n≤0) : (2:ℝ)^n≤1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hn
  have ep : 4*eps=(2:ℝ)^(-1798:ℝ) := by
    unfold eps
    rw [show (4:ℝ)=(2:ℝ)^(2:ℝ) by norm_num,←Real.rpow_add (by norm_num)]
    norm_num
  have cut : (4*eps)^(4/27:ℝ)≤(2:ℝ)^(-154:ℝ) := by
    rw [ep,←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have coef : 1024*(2:ℝ)^(-154:ℝ)=(2:ℝ)^(-144:ℝ) := by
    rw [show (1024:ℝ)=(2:ℝ)^(10:ℝ) by norm_num,←Real.rpow_add (by norm_num)]
    norm_num
  have bound := integrated_rare_walk ν M reg ht (hξ.trans (small _ (by norm_num))) F hF hδ
    (ep.trans_le (small _ (by norm_num))) (ep.symm ▸ (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)) hw
  exact bound.trans (mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_left (max_le cut hξ) (by norm_num : (0:ℝ)≤1024)).trans_eq coef) hS)

/-- Coefficients for the rectangle bound in terms of the actual two marginal masses. -/
theorem marginal_rectangle_coefficients {u v h k x m : ℝ} (hu : 0≤u) (hv : 0≤v) (hx : 0≤x)
    (hp : (27/50:ℝ)*u≤h) (hq : (27/50:ℝ)*v≤k)
    (cut : m≤sqrt (u*v)*((u*v)^(1/25:ℝ)+x)) :
    m≤2*h^(27/50:ℝ)*k^(27/50:ℝ)+2*x*sqrt (h*k) := marginal_cut hu hv hx hp hq cut

end
end PlanarUnitDistances.Competition.IncidencePiece
