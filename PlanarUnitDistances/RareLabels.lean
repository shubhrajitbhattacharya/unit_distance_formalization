import PlanarUnitDistances.RareWalk
import PlanarUnitDistances.Matching

namespace PlanarUnitDistances.Competition.IncidencePiece
open Finset Real MeasureTheory
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K] {L : Type*} [Fintype L] [Nonempty L]

def edgeProb (M : IncidencePiece K) (A : Plane×Plane → Prop) : ℝ :=
  ((M.E.filter A).card:ℝ)/M.E.card

private def frac (V : Finset Plane) (A : Plane → Prop) :=
  ((V.filter A).card:ℝ)/V.card

def pointSet (M : IncidencePiece K) (A : Plane → Prop) := M.P.filter A

private lemma pointSet_subset (M : IncidencePiece K) (A : Plane → Prop) : M.pointSet A⊆M.P :=
  filter_subset A M.P

def pointMass (M : IncidencePiece K) (A : Plane → Prop) := ∑p∈M.pointSet A,M.mu p

def centerMass (M : IncidencePiece K) (B : Plane → Prop) := ∑q∈M.Q.filter B,M.kappa q

private lemma edge_cut (M : IncidencePiece K) (A B : Plane → Prop) :
    M.edgeProb (fun e => A e.1 ∧ B e.2)=
      ((M.E∩((M.P.filter A)×ˢ(M.Q.filter B))).card:ℝ)/M.E.card := by
  unfold edgeProb
  apply congrArg (fun Z : Finset (Plane×Plane) => (Z.card:ℝ)/M.E.card)
  ext e
  simp only [mem_filter,mem_inter,mem_product]
  exact ⟨fun h => ⟨h.1,⟨(mem_product.mp (M.membership h.1)).1,h.2.1⟩,
    (mem_product.mp (M.membership h.1)).2,h.2.2⟩,fun h => ⟨h.1,h.2.1.2,h.2.2.2⟩⟩

private lemma edge_left (M : IncidencePiece K) (A : Plane → Prop) :
    M.edgeProb (fun e => A e.1)=∑p∈M.P.filter A,M.mu p := by
  have eq : M.E.filter (fun e => A e.1)=((M.P.filter A)×ˢM.Q).filter (fun e => e∈M.E) := by
    ext e
    simp only [mem_filter,mem_product]
    exact ⟨fun h => ⟨⟨⟨(mem_product.mp (M.membership h.1)).1,h.2⟩,(mem_product.mp (M.membership h.1)).2⟩,h.1⟩,
      fun h => ⟨h.2,h.1.1.2⟩⟩
  simp only [edgeProb,eq,mu,degreeP,←sum_div,natCast_card_filter,sum_product]

private lemma edge_right (M : IncidencePiece K) (B : Plane → Prop) :
    M.edgeProb (fun e => B e.2)=∑q∈M.Q.filter B,M.kappa q := by
  have eq : M.E.filter (fun e => B e.2)=(M.P×ˢ(M.Q.filter B)).filter (fun e => e∈M.E) := by
    ext e
    simp only [mem_filter,mem_product]
    exact ⟨fun h => ⟨⟨(mem_product.mp (M.membership h.1)).1,⟨(mem_product.mp (M.membership h.1)).2,h.2⟩⟩,h.1⟩,
      fun h => ⟨h.2,h.1.2.2⟩⟩
  simp only [edgeProb,eq,kappa,degreeQ,←sum_div,natCast_card_filter,sum_product_right]

omit [Nonempty L] in
private lemma total_frac (V : Finset Plane) (h : V.Nonempty) (x : Plane → L) :
    ∑a,frac V (fun p => x p=a)=1 := by
  simp only [frac,←sum_div,natCast_card_filter]
  rw [sum_comm]
  simp [eq_comm]
  exact (div_self (show (V.card:ℝ)≠0 from Nat.cast_ne_zero.mpr (card_pos.mpr h).ne')).symm

private lemma compl_frac (V : Finset Plane) (h : V.Nonempty) (A : Plane → Prop) :
    frac V (fun p => ¬A p)=1-frac V A := by
  have div := congrArg (fun n : ℕ => (n:ℝ)/V.card) (@Finset.card_filter_add_card_filter_not
    Plane V A (fun p => Classical.propDecidable (A p)) (fun p => Classical.propDecidable (¬A p)))
  have hn : (V.card:ℝ)≠0 := Nat.cast_ne_zero.mpr (card_pos.mpr h).ne'
  simp only [Nat.cast_add,add_div,div_self hn] at div
  unfold frac; linarith only [div]

private lemma low_sum (V : Finset Plane) (w : Plane → ℝ) (A : Plane → Prop)
    (hw : ∀p∈V,gamma/V.card≤w p) : gamma*frac V A ≤ ∑p∈V.filter A,w p := by
  calc
    _ = ∑_p∈V.filter A,gamma/V.card := by simp [frac,nsmul_eq_mul]; ring
    _ ≤ _ := sum_le_sum (fun p hp => hw p (mem_filter.mp hp).1)

private lemma label_mass (M : IncidencePiece K) (F : Plane×Plane → Prop) :
    labelEvent (fun _ : M.E => 1/(M.E.card:ℝ)) (fun e => F e.val)=M.edgeProb F := by
  unfold labelEvent edgeProb
  rw [sum_coe_sort M.E (fun e => if F e then 1/(M.E.card:ℝ) else 0),←sum_filter]
  simp [nsmul_eq_mul,div_eq_mul_inv]

/-- The dominant class is selected from the actual labels on both sides of
the same incidence piece, using just its regularity hypotheses. -/
theorem dominant_label (M : IncidencePiece K) {t : ℝ} (reg : Regular M t) (ht : 0<t)
    (hx : t^(-150*savingG)≤1/(2:ℝ)^100) (x y : Plane → L)
    (hs : M.edgeProb (fun e => x e.1≠y e.2)≤1/(2:ℝ)^52) :
    ∃a, M.pointMass (fun p => x p≠a)+M.centerMass (fun q => y q≠a)
      ≤2*M.edgeProb (fun e => x e.1≠y e.2) := by
  have he : (0:ℝ)<M.E.card := (Real.rpow_pos_of_pos ht _).trans_le reg.size
  obtain ⟨e,hem⟩ := card_pos.mp (Nat.cast_pos.mp he)
  have hmem := mem_product.mp (M.membership hem)
  have hP : M.P.Nonempty := ⟨_,hmem.1⟩
  have hQ : M.Q.Nonempty := ⟨_,hmem.2⟩
  have rect (A B : Plane → Prop) : M.edgeProb (fun e => A e.1 ∧ B e.2) ≤
      sqrt (frac M.P A*frac M.Q B)*((sqrt (frac M.P A*frac M.Q B))^(2/25:ℝ)+t^(-150*savingG)) := by
    rw [edge_cut]
    let z := frac M.P A*frac M.Q B
    have hz : 0≤z := by dsimp [z,frac]; positivity
    have hp : (sqrt z)^(2/25:ℝ)=z^(1/25:ℝ) := by rw [sqrt_eq_rpow,←rpow_mul hz]; norm_num
    change _≤sqrt z*((sqrt z)^(2/25:ℝ)+_)
    rw [hp]
    exact reg.rectangle _ _ (filter_subset ..) (filter_subset ..)
  let u := fun a => frac M.P (fun p => x p=a)
  let v := fun a => frac M.Q (fun q => y q=a)
  have ccP (a : L) := compl_frac M.P hP (fun p => x p=a)
  have ccQ (a : L) := compl_frac M.Q hQ (fun q => y q=a)
  have lowP (A : Plane → Prop) := (low_sum M.P M.mu A (fun p hp => (reg.point_marginal p hp).1)).trans_eq (edge_left M A).symm
  have lowQ (B : Plane → Prop) := (low_sum M.Q M.kappa B reg.center_marginal).trans_eq (edge_right M B).symm
  let w := fun _ : M.E => 1/(M.E.card:ℝ)
  have diag := matching_for_edge_law w (fun e : M.E => x e.val.1) (fun e : M.E => y e.val.2)
    u v (t^(-150*savingG)) (fun _ => div_nonneg zero_le_one he.le)
    (by simp [w,nsmul_eq_mul,div_eq_mul_inv,he.ne'])
    (fun a => by dsimp [u,frac]; positivity) (fun a => by dsimp [v,frac]; positivity)
    (total_frac M.P hP x) (total_frac M.Q hQ y) (Real.rpow_nonneg ht.le _) hx
    (fun a => (label_mass M _).trans_le (rect (fun p => x p=a) (fun q => y q=a)))
    (fun a => (label_mass M (fun e => x e.1≠a ∧ y e.2≠a)).trans_le
      (by simpa only [ccP,ccQ] using rect (fun p => x p≠a) (fun q => y q≠a)))
    (fun a => (by simpa only [ccP] using lowP (fun p => x p≠a) :
      gamma*(1-u a)≤M.edgeProb (fun e => x e.1≠a)).trans_eq
        (label_mass M (fun e => x e.1≠a)).symm)
    (fun a => (by simpa only [ccQ] using lowQ (fun q => y q≠a) :
      gamma*(1-v a)≤M.edgeProb (fun e => y e.2≠a)).trans_eq
        (label_mass M (fun e => y e.2≠a)).symm)
  obtain ⟨a,ha⟩ := diag.1 ((label_mass M _).trans_le hs)
  refine ⟨a,?_⟩
  have lp := (label_mass M (fun e => x e.1≠a)).trans (edge_left M (fun p => x p≠a))
  have lq := (label_mass M (fun e => y e.2≠a)).trans (edge_right M (fun q => y q≠a))
  exact (congrArg₂ (·+·) lp.symm lq.symm).trans_le
    (ha.trans_eq (congrArg (2*·) (label_mass M (fun e => x e.1≠y e.2))))

def labelMismatch (M : IncidencePiece K) (r : (Plane → L)×(Plane → L)) : ℝ :=
  M.edgeProb (fun e => r.1 e.1≠r.2 e.2)

/-- Choose the same dominant label for the point and center side at each
level. The integrated two-neighbor coincidence bound then follows directly
from bounds on label mismatch, without a supplied exceptional family. -/
theorem dominant_rare_walk {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν]
    (M : IncidencePiece K) {t S : ℝ} (reg : Regular M t) (ht : 0<t) (hS : 0≤S)
    (hx : t^(-150*savingG)≤(2:ℝ)^(-154:ℝ))
    (R : SimpleFunc Ω ((Plane → L)×(Plane → L)))
    (hs : ∀s,M.labelMismatch (R s)≤2*eps) (hw : (∫s,M.labelMismatch (R s) ∂ν)≤2*S) :
    ∃a : SimpleFunc Ω L, (∀s,
      M.pointMass (fun p => (R s).1 p≠a s)+M.centerMass (fun q => (R s).2 q≠a s)
        ≤ 2*M.labelMismatch (R s)) ∧
      (∫s,∑v : Triple M, if (R s).1 v.1.val≠a s ∧ (R s).1 v.2.2.val≠a s then M.mass v else 0 ∂ν)
         ≤ (2:ℝ)^(-144:ℝ)*S := by
  have toNat (n : ℕ) : (2:ℝ)^(-(n:ℝ))=1/(2:ℝ)^n := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast,one_div]
  have hx100 : t^(-150*savingG)≤1/(2:ℝ)^100 := by
    rw [←toNat]
    exact hx.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  have e52 : 2*eps≤1/(2:ℝ)^52 := by
    calc
      _ = (2:ℝ)^(1:ℝ)*2^(-1800:ℝ) := by rw [Real.rpow_one]; rfl
      _ = (2:ℝ)^(-1799:ℝ) := by rw [←Real.rpow_add (by norm_num)]; norm_num
      _ ≤ 2^(-(52:ℕ):ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := toNat 52
  have choice (r : (Plane → L)×(Plane → L)) : ∃a : L, M.labelMismatch r≤2*eps →
      M.pointMass (fun p => r.1 p≠a)+M.centerMass (fun q => r.2 q≠a) ≤2*M.labelMismatch r := by
    by_cases h : M.labelMismatch r≤2*eps
    · obtain ⟨a,ha⟩ := dominant_label M reg ht hx100 r.1 r.2 (h.trans e52)
      exact ⟨a,fun _ => ha⟩
    · exact ⟨Classical.choice (inferInstance : Nonempty L),fun hn => (h hn).elim⟩
  choose d hd using choice
  refine ⟨R.map d, fun s => hd _ (hs s),?_⟩
  let F (r : (Plane → L)×(Plane → L)) := M.pointSet (fun p => r.1 p≠d r)
  let H (r : (Plane → L)×(Plane → L)) := ∑p∈F r,M.mu p
  have point (s : Ω) : H (R s)≤2*M.labelMismatch (R s) :=
    (le_add_of_nonneg_right (sum_nonneg (fun q _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))).trans
      (hd _ (hs s))
  have intH : Integrable (fun s => H (R s)) ν := (R.map H).integrable_of_isFiniteMeasure
  have intM : Integrable (fun s => M.labelMismatch (R s)) ν :=
    (R.map (labelMismatch M)).integrable_of_isFiniteMeasure
  have intBound := integral_mono intH (intM.const_mul 2) point
  rw [integral_const_mul] at intBound
  have hh (s : Ω) : H (R s)≤4*eps := (point s).trans
    ((mul_le_mul_of_nonneg_left (hs s) (by norm_num : (0:ℝ)≤2)).trans_eq (by ring))
  have walk := rare_walk_budget ν M reg ht hS hx (R.map F) (fun _ => pointSet_subset M _)
    hh (intBound.trans ((mul_le_mul_of_nonneg_left hw (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)))
  apply le_trans _ walk
  apply le_of_eq
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  apply sum_congr rfl
  intro v _
  by_cases hv : (R s).1 v.1.val≠d (R s) ∧ (R s).1 v.2.2.val≠d (R s) <;>
    simp [SimpleFunc.map_apply,F,pointSet,v.1.prop,v.2.2.prop,hv]

private lemma joint_exception (M : IncidencePiece K) {t : ℝ} (reg : Regular M t) (ht : 0<t)
    (A B : Plane → Prop) (H : ℝ)
    (mass : M.pointMass A+M.centerMass B≤H) (small : H≤4*eps) :
    M.edgeProb (fun e => A e.1 ∧ B e.2) ≤
      ((9/8)*(2:ℝ)^(-144:ℝ)+t^(-150*savingG))*H := by
  let u := frac M.P A
  let v := frac M.Q B
  let b := sqrt (u*v)
  have hu : 0≤u := by dsimp [u,frac]; positivity
  have hv : 0≤v := by dsimp [v,frac]; positivity
  have bu : b≤(u+v)/2 := by
    dsimp only [b]; rw [sqrt_mul hu]
    nlinarith only [sq_nonneg (sqrt u-sqrt v),sq_sqrt hu,sq_sqrt hv]
  have pu := low_sum M.P M.mu A (fun p hp => (reg.point_marginal p hp).1)
  have qv := low_sum M.Q M.kappa B reg.center_marginal
  change (27/50:ℝ)*u≤_ at pu
  change (27/50:ℝ)*v≤_ at qv
  change (∑p∈M.P.filter A,M.mu p)+(∑q∈M.Q.filter B,M.kappa q)≤H at mass
  have bh : b≤H := by linarith only [bu,pu,qv,hu,hv,mass]
  have rad : (4*eps)^(2/25:ℝ)≤(9/8)*(2:ℝ)^(-144:ℝ) := by
    have raw : 4*eps=(2:ℝ)^(-1798:ℝ) := by
      unfold eps
      rw [show (4:ℝ)=(2:ℝ)^(2:ℝ) by norm_num,←Real.rpow_add (by norm_num)]; norm_num
    have root : (2:ℝ)^(4/25:ℝ)≤9/8 := by
      apply le_of_pow_le_pow_left₀ (n:=25) (by decide) (by norm_num)
      rw [←Real.rpow_natCast ((2:ℝ)^(4/25:ℝ)) 25,←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
      norm_num
    rw [raw,←rpow_mul (by norm_num : (0:ℝ)≤2),show (-1798:ℝ)*(2/25)=4/25+(-144) by norm_num,
      rpow_add (by norm_num : (0:ℝ)<2)]
    exact mul_le_mul_of_nonneg_right root (rpow_nonneg (by norm_num) _)
  have br : b^(2/25:ℝ)≤(9/8)*(2:ℝ)^(-144:ℝ) :=
    (rpow_le_rpow (sqrt_nonneg _) (bh.trans small) (by norm_num)).trans rad
  have pw : b^(2/25:ℝ)=(u*v)^(1/25:ℝ) := by
    dsimp only [b]; rw [sqrt_eq_rpow,←rpow_mul (mul_nonneg hu hv)]; norm_num
  rw [edge_cut]
  have bound := reg.rectangle _ _ (filter_subset A M.P) (filter_subset B M.Q)
  change _≤b*((u*v)^(1/25:ℝ)+t^(-150*savingG)) at bound
  rw [←pw] at bound
  exact bound.trans ((mul_le_mul bh (add_le_add br le_rfl)
    (add_nonneg (rpow_nonneg (sqrt_nonneg _) _) (rpow_nonneg ht.le _)) ((sqrt_nonneg _).trans bh)).trans_eq (mul_comm ..))

/-- The two coincidence estimates (cb:je-jw) hold for one measurable
dominant label on the regular incidence piece and one level measure.
Both the edge law and the two-edge path law are the actual laws of M. -/
theorem rare_edge_and_walk {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν]
    (M : IncidencePiece K) {t S : ℝ} (reg : Regular M t) (ht : 0<t) (hS : 0≤S)
    (hx : t^(-150*savingG)≤(2:ℝ)^(-154:ℝ))
    (R : SimpleFunc Ω ((Plane → L)×(Plane → L)))
    (hs : ∀s,M.labelMismatch (R s)≤2*eps) (hw : (∫s,M.labelMismatch (R s) ∂ν)≤2*S) :
    ∃a : SimpleFunc Ω L, (∀s,
      M.pointMass (fun p => (R s).1 p≠a s)+M.centerMass (fun q => (R s).2 q≠a s)
        ≤ 2*M.labelMismatch (R s)) ∧
      (∫s,M.edgeProb (fun e => (R s).1 e.1≠a s ∧ (R s).2 e.2≠a s) ∂ν)
        ≤ 5*(2:ℝ)^(-144:ℝ)*S ∧
      (∫s,∑v : Triple M, if (R s).1 v.1.val≠a s ∧ (R s).1 v.2.2.val≠a s then M.mass v else 0 ∂ν)
        ≤ (2:ℝ)^(-144:ℝ)*S := by
  obtain ⟨a,ha,hwalk⟩ := dominant_rare_walk ν M reg ht hS hx R hs hw
  refine ⟨a,ha,?_,hwalk⟩
  let c := (9/8)*(2:ℝ)^(-144:ℝ)+t^(-150*savingG)
  let J (r : ((Plane → L)×(Plane → L))×L) :=
    M.edgeProb (fun e => r.1.1 e.1≠r.2 ∧ r.1.2 e.2≠r.2)
  have intJ : Integrable (fun s => J (R s,a s)) ν :=
    ((R.pair a).map J).integrable_of_isFiniteMeasure
  have intM : Integrable (fun s => M.labelMismatch (R s)) ν :=
    (R.map (labelMismatch M)).integrable_of_isFiniteMeasure
  have point (s : Ω) : J (R s,a s) ≤ (2*c)*M.labelMismatch (R s) := by
    apply (joint_exception M reg ht (fun p => (R s).1 p≠a s) (fun q => (R s).2 q≠a s)
      (2*M.labelMismatch (R s)) (ha s)
      ((mul_le_mul_of_nonneg_left (hs s) (by norm_num : (0:ℝ)≤2)).trans_eq (by ring))).trans_eq
    dsimp only [c]; ring
  have hi := integral_mono intJ (intM.const_mul (2*c)) point
  rw [integral_const_mul] at hi
  have hc : 0≤2*c := by dsimp only [c]; positivity
  have num : ((9/8)*(2:ℝ)^(-144:ℝ)+2^(-154:ℝ))*4≤5*2^(-144:ℝ) := by norm_num
  have coeff : c*4≤5*(2:ℝ)^(-144:ℝ) :=
    (mul_le_mul_of_nonneg_right (add_le_add le_rfl hx) (by norm_num : (0:ℝ)≤4)).trans num
  calc
    _ ≤ (2*c)*(2*S) := hi.trans (mul_le_mul_of_nonneg_left hw hc)
    _ = (c*4)*S := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right coeff hS

/-- The incidence estimate in terms of actual edge probabilities of the
two fixed endpoint events, for every predicate on each vertex class. -/
theorem edgeProb_rectangle_marginals (M : IncidencePiece K) {t : ℝ} (reg : Regular M t)
    (ht : 0<t) (A B : Plane → Prop) :
    M.edgeProb (fun e => A e.1 ∧ B e.2) ≤
      2*(M.edgeProb (fun e => A e.1))^(27/50:ℝ)*(M.edgeProb (fun e => B e.2))^(27/50:ℝ)+
      2*t^(-150*savingG)*sqrt (M.edgeProb (fun e => A e.1)*M.edgeProb (fun e => B e.2)) := by
  rw [edge_cut M A B]
  apply marginal_rectangle_coefficients (u := frac M.P A) (v := frac M.Q B)
    (by unfold frac; positivity) (by unfold frac; positivity) (Real.rpow_nonneg ht.le _)
  · rw [edge_left]; exact low_sum M.P M.mu A (fun p hp => (reg.point_marginal p hp).1)
  · rw [edge_right]; exact low_sum M.Q M.kappa B reg.center_marginal
  · exact reg.rectangle (M.P.filter A) (M.Q.filter B) (filter_subset ..) (filter_subset ..)

theorem edgeProb_point_event (M : IncidencePiece K) (A : Plane → Prop) :
    M.edgeProb (fun e => A e.1)=M.pointMass A := edge_left M A
theorem edgeProb_center_event (M : IncidencePiece K) (A : Plane → Prop) :
    M.edgeProb (fun e => A e.2)=M.centerMass A := edge_right M A

end
end PlanarUnitDistances.Competition.IncidencePiece
