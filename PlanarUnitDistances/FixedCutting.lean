/- Adapted from OpenAI math, UnitDistances/Powers.lean, commit
   adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0).
   The cutting and trimming exponents below retain the fixed input deficit g. -/
import PlanarUnitDistances.CircleRegularization
import PlanarUnitDistances.Counting

namespace OAI

namespace PlanarUnitDistances.PowerGrowth
open Filter

def Lower {ι : Type*} (F : Filter ι) (t f : ι → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ i in F, t i ^ (a-ε) ≤ f i

def Upper {ι : Type*} (F : Filter ι) (t f : ι → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ i in F, f i ≤ t i ^ (a+ε)

variable {ι : Type*} {F : Filter ι} {t f g : ι → ℝ} {a b : ℝ}

lemma Lower.mono (hf : Lower F t f a) (h : f ≤ᶠ[F] g) : Lower F t g a := by
  intro ε hε
  filter_upwards [hf ε hε,h] with i hi hfg
  exact hi.trans hfg

lemma Upper.mono (hg : Upper F t g a) (h : f ≤ᶠ[F] g) : Upper F t f a := by
  intro ε hε
  filter_upwards [hg ε hε,h] with i hi hfg
  exact hfg.trans hi


lemma eventually_one_le (ht : Tendsto t F atTop) : ∀ᶠ i in F,1 ≤ t i :=
  ht.eventually_ge_atTop 1

lemma eventually_base_pos (ht : Tendsto t F atTop) : ∀ᶠ i in F,0 < t i :=
  (eventually_one_le ht).mono fun _ hi => lt_of_lt_of_le zero_lt_one hi


lemma Upper.exponent_mono (hf : Upper F t f a) (h : a ≤ b)
    (ht : Tendsto t F atTop) : Upper F t f b := by
  intro ε hε
  filter_upwards [hf ε hε,eventually_one_le ht] with i hi hti
  exact hi.trans (Real.rpow_le_rpow_of_exponent_le hti (by linarith))

lemma Lower.eventually_pos (hf : Lower F t f a) (ht : Tendsto t F atTop) :
    ∀ᶠ i in F,0 < f i := by
  filter_upwards [hf 1 zero_lt_one,eventually_base_pos ht] with i hi hti
  exact (Real.rpow_pos_of_pos hti _).trans_le hi


lemma Upper.mul (hf : Upper F t f a) (hg : Upper F t g b)
    (hnf : ∀ᶠ i in F,0 ≤ f i) (hng : ∀ᶠ i in F,0 ≤ g i)
    (ht : Tendsto t F atTop) : Upper F t (fun i => f i*g i) (a+b) := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),hg (ε/2) (by positivity),hnf,hng,eventually_base_pos ht]
    with i hi hj _ hj0 hti
  have he : a+b+ε=(a+ε/2)+(b+ε/2) := by ring
  rw [he,Real.rpow_add hti]
  exact mul_le_mul hi hj hj0 (Real.rpow_nonneg hti.le _)

lemma eventually_constant_le_rpow (ht : Tendsto t F atTop) {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ∀ᶠ i in F,C ≤ t i ^ ε := by
  exact (_root_.tendsto_rpow_atTop hε |>.comp ht).eventually_ge_atTop C

lemma Lower.const_mul (hf : Lower F t f a) (ht : Tendsto t F atTop)
    {C : ℝ} (hC : 0 < C) : Lower F t (fun i => C*f i) a := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),eventually_constant_le_rpow ht
    (show 0<ε/2 by positivity) C⁻¹,eventually_base_pos ht] with i hi hc hti
  have hc' : 1 ≤ C*(t i)^(ε/2) := by simpa only [mul_comm] using (inv_le_iff_one_le_mul₀ hC).mp hc
  have he : a-ε/2=(a-ε)+ε/2 := by ring
  have hpos := Real.rpow_nonneg hti.le (a-ε)
  calc
    (t i)^(a-ε) ≤ (t i)^(a-ε)*(C*(t i)^(ε/2)) := le_mul_of_one_le_right hpos hc'
    _ = C*(t i)^(a-ε/2) := by
      conv_rhs => rw [he,Real.rpow_add hti]
      ring
    _ ≤ C*f i := mul_le_mul_of_nonneg_left hi hC.le

lemma Upper.const_mul (hf : Upper F t f a) (ht : Tendsto t F atTop)
    {C : ℝ} (hC : 0 ≤ C) : Upper F t (fun i => C*f i) a := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),eventually_constant_le_rpow ht
    (show 0<ε/2 by positivity) C,eventually_base_pos ht] with i hi hc hti
  have he : a+ε=ε/2+(a+ε/2) := by ring
  calc
    C*f i ≤ C*(t i)^(a+ε/2) := mul_le_mul_of_nonneg_left hi hC
    _ ≤ (t i)^(ε/2)*(t i)^(a+ε/2) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hti.le _)
    _ = (t i)^(a+ε) := by rw [he]; exact (Real.rpow_add hti _ _).symm

lemma Upper.add (hf : Upper F t f a) (hg : Upper F t g a)
    (ht : Tendsto t F atTop) : Upper F t (fun i => f i+g i) a := by
  have hmax : Upper F t (fun i => max (f i) (g i)) a := by
    intro ε hε
    filter_upwards [hf ε hε,hg ε hε] with i hi hj
    exact max_le hi hj
  exact (hmax.const_mul ht (show (0:ℝ)≤2 by norm_num)).mono
    (Eventually.of_forall fun i => by dsimp; linarith [le_max_left (f i) (g i),le_max_right (f i) (g i)])

lemma Lower.div (hf : Lower F t f a) (hg : Upper F t g b)
    (hng : ∀ᶠ i in F,0 < g i) (ht : Tendsto t F atTop) :
    Lower F t (fun i => f i/g i) (a-b) := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),hg (ε/2) (by positivity),hng,eventually_base_pos ht]
    with i hi hj hj0 hti
  have he : a-b-ε=(a-ε/2)-(b+ε/2) := by ring
  rw [he,Real.rpow_sub hti]
  exact div_le_div₀ ((Real.rpow_nonneg hti.le _).trans hi) hi hj0 hj


end PlanarUnitDistances.PowerGrowth

namespace PlanarUnitDistances.PowerGrowth
open Filter
variable {ι : Type*} {F : Filter ι} {t f g : ι → ℝ} {a b : ℝ}

lemma upper_rpow (ht : Tendsto t F atTop) (a : ℝ) :
    Upper F t (fun i => t i^a) a := by
  intro ε hε
  filter_upwards [eventually_one_le ht] with i hi
  exact Real.rpow_le_rpow_of_exponent_le hi (by linarith)
lemma lower_rpow (ht : Tendsto t F atTop) (a : ℝ) :
    Lower F t (fun i => t i^a) a := by
  intro ε hε
  filter_upwards [eventually_one_le ht] with i hi
  exact Real.rpow_le_rpow_of_exponent_le hi (by linarith)
lemma upper_const (ht : Tendsto t F atTop) (c : ℝ) : Upper F t (fun _ => c) 0 := by
  intro ε hε
  simpa only [zero_add] using eventually_constant_le_rpow ht hε c

lemma Upper.div (hf : Upper F t f a) (hg : Lower F t g b)
    (hng : ∀ᶠi in F,0<g i) (ht : Tendsto t F atTop) :
    Upper F t (fun i => f i/g i) (a-b) := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),hg (ε/2) (by positivity),hng,eventually_base_pos ht]
    with i hi hj hj0 hti
  have he : a-b+ε=(a+ε/2)-(b-ε/2) := by ring
  rw [he,Real.rpow_sub hti]
  exact div_le_div₀ (Real.rpow_nonneg hti.le _) hi (Real.rpow_pos_of_pos hti _) hj

lemma Upper.rpow (hf : Upper F t f a) (hnf : ∀ᶠi in F,0≤f i)
    (ht : Tendsto t F atTop) {c : ℝ} (hc : 0<c) :
    Upper F t (fun i => f i^c) (a*c) := by
  intro ε hε
  filter_upwards [hf (ε/c) (div_pos hε hc),hnf,eventually_base_pos ht] with i hi hi0 hti
  have hh := Real.rpow_le_rpow hi0 hi hc.le
  rw [←Real.rpow_mul hti.le] at hh
  convert hh using 1
  congr 1
  field_simp


lemma Upper.tendsto_zero (hf : Upper F t f a) (hnf : ∀ᶠi in F,0≤f i)
    (ht : Tendsto t F atTop) (ha : a<0) : Tendsto f F (nhds 0) := by
  have hb := hf (-a/2) (by linarith)
  have he : a+ -a/2=a/2 := by ring
  rw [he] at hb
  have hz : Tendsto (fun x : ℝ => x^(a/2)) atTop (nhds 0) := by
    have he' : -(-a/2)=a/2 := by ring
    simpa only [he'] using (_root_.tendsto_rpow_neg_atTop (by linarith : 0 < -a/2))
  exact squeeze_zero' hnf hb (hz.comp ht)

lemma Upper.ratio_zero (hf : Upper F t f a) (hg : Lower F t g b)
    (hnf : ∀ᶠi in F,0≤f i) (ht : Tendsto t F atTop) (hab : a<b) :
    Tendsto (fun i => f i/g i) F (nhds 0) := by
  have hg0 := hg.eventually_pos ht
  exact (hf.div hg hg0 ht).tendsto_zero
    (by filter_upwards [hnf,hg0] with i hi hj; exact div_nonneg hi hj.le) ht (sub_neg.mpr hab)

lemma upper_log (ht : Tendsto t F atTop) : Upper F t (fun i => Real.log (t i)) 0 := by
  intro ε hε
  have hh := (_root_.isLittleO_log_rpow_atTop hε).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [ht.eventually hh,eventually_base_pos ht] with i hi hti
  apply (le_abs_self (Real.log (t i))).trans
  simpa only [Real.norm_eq_abs,one_mul,abs_of_nonneg (Real.rpow_nonneg hti.le ε),zero_add] using hi

lemma Upper.log (hf : Upper F t f a) (hfp : ∀ᶠi in F,0<f i)
    (ht : Tendsto t F atTop) (ha : 0≤a) : Upper F t (fun i => Real.log (f i)) 0 := by
  apply ((upper_log ht).const_mul ht (show 0≤a+1 by linarith)).mono
  filter_upwards [hf 1 zero_lt_one,hfp,eventually_base_pos ht] with i hi hfi hti
  have hh := Real.log_le_log hfi hi
  simpa only [Real.log_rpow hti] using hh

lemma Lower.of_loss (hg : Lower F t g a) {h : ι → ℝ} (hh : Upper F t h b)
    (hh0 : ∀ᶠi in F,0≤h i) (ht : Tendsto t F atTop) (hab : b<a)
    (hle : ∀ᶠi in F,g i≤f i+h i) : Lower F t f a := by
  have hlim := hh.ratio_zero hg hh0 ht hab
  have hsmall : ∀ᶠi in F,h i/g i≤1/2 := hlim.eventually_le_const (by norm_num)
  apply (hg.const_mul ht (by norm_num : (0:ℝ)<1/2)).mono
  filter_upwards [hsmall,hg.eventually_pos ht,hle] with i hi hgi hle
  have hh' := (div_le_iff₀ hgi).mp hi
  linarith

end PlanarUnitDistances.PowerGrowth
namespace PlanarUnitDistances.CuttingAsymptotics
open Filter PowerGrowth CircleIncidence CircleCutting
open scoped Classical
noncomputable section

variable {ι : Type*} {filter : Filter ι}

lemma cuttingLog_upper {t : ι → ℝ} {X : ι → Finset Plane}
    (ht : Tendsto t filter atTop)
    (hX : Upper filter t (fun i => ((X i).card:ℝ)) 3) :
    Upper filter t (fun i => cuttingLog (X i).card) 0 := by
  have h1 := (upper_const ht 1).exponent_mono (by norm_num : (0:ℝ)≤3) ht
  have hs := h1.add hX ht
  have hp := hs.rpow (Eventually.of_forall fun i => by positivity) ht (by norm_num : (0:ℝ)<6)
  have hp' : Upper filter t (fun i => 81*(1+((X i).card:ℝ))^6) 18 := by
    convert hp.const_mul ht (by norm_num : (0:ℝ)≤81) using 1
    · ext i; exact congrArg (81*·) (Real.rpow_natCast (1+((X i).card:ℝ)) 6).symm
    · norm_num
  have ho := hp'.add ((upper_const ht 1).exponent_mono (by norm_num : (0:ℝ)≤18) ht) ht
  have hq := ho.const_mul ht (by norm_num : (0:ℝ)≤10)
  exact hq.log (Eventually.of_forall fun i => by positivity) ht (by norm_num)

theorem exists_cut_fixed_deficit {t : ι → ℝ} (X : ι → Finset Plane)
    (ht : Tendsto t filter atTop) (ht1 : ∀i,1≤t i) (hX0 : ∀i,(X i).Nonempty)
    (hX : Upper filter t (fun i => ((X i).card:ℝ)) 3)
    (hcard : ∀i,((X i).card:ℝ)=(t i)^3)
    {g a : ℝ} (hE : Lower filter t (fun i => incidences (X i) (X i)) (4-g))
    (hga : g<a) (ha : 0<a) (ha1 : a<1) :
    ∃P Q : ι → Finset Plane,(∀i,P i⊆X i ∧ Q i⊆X i) ∧
      (∀i,((P i).card:ℝ)≤2*(t i)^(1+2*a)) ∧
      (∀i,((Q i).card:ℝ)≤(t i)^(2+a)) ∧
      Upper filter t (fun i => ((P i).card:ℝ)) (1+2*a) ∧
      Upper filter t (fun i => ((Q i).card:ℝ)) (2+a) ∧
      Lower filter t (fun i => incidences (P i) (Q i)) (2+2*a-g) := by
  let R : ι → ℝ := fun i => (t i)^(1-a)
  let B : ι → ℕ := fun i => Nat.ceil ((t i)^(1+2*a))
  have ht0 (i : ι) : 0<t i := zero_lt_one.trans_le (ht1 i)
  have hRp (i : ι) : 0<R i := Real.rpow_pos_of_pos (ht0 i) _
  have hBp (i : ι) : 0<B i := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (ht0 i) _)
  choose P hP Q hQ hcP hcQ hc using fun i =>
    exists_incidence_piece (X i) (X i) (hX0 i) (hRp i) (hBp i)
  have hR : Upper filter t R (1-a) := upper_rpow ht _
  have hRl : Lower filter t R (1-a) := lower_rpow ht _
  have hBu : Upper filter t (fun i => (B i:ℝ)) (1+2*a) := by
    apply ((upper_rpow ht (1+2*a)).add
      ((upper_const ht 2).exponent_mono (by linarith : 0≤1+2*a) ht) ht).mono
    exact Eventually.of_forall fun i => by
      have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg (ht0 i).le (1+2*a))
      dsimp [B]
      linarith
  have hBl : Lower filter t (fun i => (B i:ℝ)) (1+2*a) := by
    apply (lower_rpow ht (1+2*a)).mono
    exact Eventually.of_forall fun i => by
      have hh := Nat.le_ceil ((t i)^(1+2*a))
      dsimp [B]
      linarith
  have hPu : Upper filter t (fun i => ((P i).card:ℝ)) (1+2*a) :=
    hBu.mono (Eventually.of_forall fun i => Nat.cast_le.mpr (hcP i))
  have hQu : Upper filter t (fun i => ((Q i).card:ℝ)) (2+a) := by
    have hh := (hX.div hRl (Eventually.of_forall hRp) ht).mono (Eventually.of_forall hcQ)
    convert hh using 1; ring
  let S : ι → ℝ := fun i => R i*cuttingLog (X i).card+1
  have hln := cuttingLog_upper ht hX
  have hSu : Upper filter t S (1-a) := by
    have hh := hR.mul hln (Eventually.of_forall fun i => (hRp i).le)
      (Eventually.of_forall fun i => zero_le_one.trans (cuttingLog_one_le _)) ht
    simp only [add_zero] at hh
    exact hh.add ((upper_const ht 1).exponent_mono (by linarith : 0≤1-a) ht) ht
  have hS0 (i : ι) : 0≤S i := by
    dsimp [S]
    exact add_nonneg (mul_nonneg (hRp i).le (zero_le_one.trans (cuttingLog_one_le _))) zero_le_one
  let K : ι → ℝ := fun i => 43*(1+(S i)^2)+((X i).card:ℝ)/(B i:ℝ)
  have hKp (i : ι) : 0<K i := by dsimp [K]; positivity
  have hKu : Upper filter t K (2-2*a) := by
    have hs2 := hSu.mul hSu (Eventually.of_forall hS0) (Eventually.of_forall hS0) ht
    have hs2' : Upper filter t (fun i => (S i)^2) (2-2*a) := by
      convert hs2 using 1 <;> ring_nf
    have hu := ((upper_const ht 1).exponent_mono (by linarith : 0≤2-2*a) ht).add hs2' ht
    have hv := hX.div hBl (Eventually.of_forall fun i => Nat.cast_pos.mpr (hBp i)) ht
    have hv' : Upper filter t (fun i => ((X i).card:ℝ)/(B i:ℝ)) (2-2*a) := by
      convert hv using 1; ring
    exact (hu.const_mul ht (by norm_num : (0:ℝ)≤43)).add hv' ht
  let loss : ι → ℝ := fun i => S i*(((X i).card:ℝ)+2*(X i).card)
  have hlu : Upper filter t loss (4-a) := by
    have hn := hX.add (hX.const_mul ht (by norm_num : (0:ℝ)≤2)) ht
    have hh := hSu.mul hn (Eventually.of_forall hS0)
      (Eventually.of_forall fun i => by positivity) ht
    convert hh using 1; ring
  have hkeep : Lower filter t (fun i => K i*incidences (P i) (Q i)) (4-g) :=
    hE.of_loss hlu (Eventually.of_forall fun i => mul_nonneg (hS0 i) (by positivity)) ht
      (by linarith) (Eventually.of_forall fun i => by
        have hh := hc i
        change incidences (X i) (X i) ≤ loss i+K i*incidences (P i) (Q i) at hh
        linarith)
  have hfinal := hkeep.div hKu (Eventually.of_forall hKp) ht
  have hfinal' : Lower filter t (fun i => incidences (P i) (Q i)) (2+2*a-g) := by
    have he : (fun i => K i*incidences (P i) (Q i)/K i) =
        (fun i => incidences (P i) (Q i)) := by
      funext i
      exact mul_div_cancel_left₀ _ (hKp i).ne'
    rw [he] at hfinal
    convert hfinal using 1; ring
  refine ⟨P,Q,fun i => ⟨hP i,hQ i⟩,?_,?_,hPu,hQu,hfinal'⟩
  · intro i
    have hb := Nat.ceil_lt_add_one (Real.rpow_nonneg (ht0 i).le (1+2*a))
    have hv := Real.one_le_rpow (ht1 i) (by linarith : 0≤1+2*a)
    have h := (Nat.cast_le.mpr (hcP i) : ((P i).card:ℝ)≤(B i:ℝ))
    dsimp only [B] at h
    linarith
  · intro i
    have h := hcQ i
    dsimp only [R] at h
    rw [hcard i, ← Real.rpow_natCast (t i) 3, ← Real.rpow_sub (ht0 i)] at h
    simpa only [Nat.cast_ofNat, show (3:ℝ)-(1-a)=2+a by ring] using h
end
end PlanarUnitDistances.CuttingAsymptotics
namespace PlanarUnitDistances.CuttingAsymptotics
open Filter PowerGrowth CircleIncidence CircleCutting
open scoped Classical
noncomputable section

variable {ι : Type*} {filter : Filter ι}

lemma incidence_upper {t : ι → ℝ} {X P Q : ι → Finset Plane}
    (ht : Tendsto t filter atTop)
    (hX : Upper filter t (fun i => ((X i).card:ℝ)) 3)
    (hPX : ∀i,P i⊆X i) (hQX : ∀i,Q i⊆X i)
    {m n e : ℝ} (hP : Upper filter t (fun i => ((P i).card:ℝ)) m)
    (hQ : Upper filter t (fun i => ((Q i).card:ℝ)) n)
    (hm : m≤e) (hn : n≤e) (hmn : (m+n)*(2/3:ℝ)≤e) :
    Upper filter t (fun i => incidences (P i) (Q i)) e := by
  have hlog := cuttingLog_upper ht hX
  have hLp := hlog.mul hlog
    (Eventually.of_forall fun i => zero_le_one.trans (cuttingLog_one_le _))
    (Eventually.of_forall fun i => zero_le_one.trans (cuttingLog_one_le _)) ht
  have hL : Upper filter t (fun i => 1000*(cuttingLog (X i).card)^2) 0 := by
    have hh := hLp.const_mul ht (by norm_num : (0:ℝ)≤1000)
    convert hh using 1 <;> ring_nf
  have hprod := hP.mul hQ (Eventually.of_forall fun _ => Nat.cast_nonneg _)
    (Eventually.of_forall fun _ => Nat.cast_nonneg _) ht
  have hmixed := (hprod.rpow (Eventually.of_forall fun i => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    ht (by norm_num : (0:ℝ)<2/3)).exponent_mono hmn ht
  have hsum := (hmixed.add (hP.exponent_mono hm ht) ht).add (hQ.exponent_mono hn ht) ht
  have htot := hL.mul hsum (Eventually.of_forall fun i => by positivity)
    (Eventually.of_forall fun i => by positivity) ht
  simp only [zero_add] at htot
  apply htot.mono
  exact Eventually.of_forall fun i => incidence_bound_enlarged (P i) (Q i)
    (cuttingLog_one_le _) (cuttingLog_mono (Finset.card_le_card (hPX i)))
      (cuttingLog_mono (Finset.card_le_card (hQX i))) le_rfl le_rfl

theorem trim_fixed_deficit {t : ι → ℝ} {X P Q : ι → Finset Plane}
    (ht : Tendsto t filter atTop) (ht1 : ∀i,1≤t i)
    (hX : Upper filter t (fun i => ((X i).card:ℝ)) 3)
    (hPX : ∀i,P i⊆X i) (hQX : ∀i,Q i⊆X i)
    {a b g : ℝ} (hgb : g<b/2) (_ha : 0<a) (ha1 : a<1) (hb : 0<b) (hba : b<a)
    (hP : Upper filter t (fun i => ((P i).card:ℝ)) (1+2*a))
    (hQ : Upper filter t (fun i => ((Q i).card:ℝ)) (2+a))
    (hE : Lower filter t (fun i => incidences (P i) (Q i)) (2+2*a-g)) :
    ∃F G : ι → Finset Plane,(∀i,F i⊆P i ∧ G i⊆Q i) ∧
      (∀i,∀p∈F i,degree (G i) p≤(t i)^(1+b)) ∧
      (∀i,∀q∈G i,degree (F i) q≤(t i)^(a+b)) ∧
      Upper filter t (fun i => ((F i).card:ℝ)) (1+2*a) ∧
      Upper filter t (fun i => ((G i).card:ℝ)) (2+a) ∧
      Lower filter t (fun i => incidences (F i) (G i)) (2+2*a-g) := by
  have ht0 (i : ι) : 0<t i := zero_lt_one.trans_le (ht1 i)
  let L : ι → ℝ := fun i => cuttingLog (X i).card
  let A : ι → ℝ := fun i => (t i)^(1+b)
  let B : ι → ℝ := fun i => (t i)^(a+b)
  have hAp (i : ι) : 0<A i := Real.rpow_pos_of_pos (ht0 i) _
  have hBp (i : ι) : 0<B i := Real.rpow_pos_of_pos (ht0 i) _
  choose F hF G hG hdF hdG he using fun i => exists_trimmed (P i) (Q i)
    (hAp i) (hBp i) (cuttingLog_one_le (X i).card)
    (cuttingLog_mono (Finset.card_le_card (hPX i))) (cuttingLog_mono (Finset.card_le_card (hQX i)))
  have hEu : Upper filter t (fun i => incidences (P i) (Q i)) (2+2*a) :=
    incidence_upper ht hX hPX hQX hP hQ (by linarith) (by linarith) (by ring_nf; rfl)
  have hlog := cuttingLog_upper ht hX
  have hLp := hlog.mul hlog
    (Eventually.of_forall fun i => zero_le_one.trans (cuttingLog_one_le _))
    (Eventually.of_forall fun i => zero_le_one.trans (cuttingLog_one_le _)) ht
  have hLu : Upper filter t (fun i => 1000*(L i)^2) 0 := by
    dsimp only [L]
    have hh := hLp.const_mul ht (by norm_num : (0:ℝ)≤1000)
    convert hh using 1 <;> ring_nf
  have hEA := hEu.div (lower_rpow ht (1+b)) (Eventually.of_forall hAp) ht
  have hEB := hEu.div (lower_rpow ht (a+b)) (Eventually.of_forall hBp) ht
  have hEA0 : ∀ᶠi in filter,0≤ incidences (P i) (Q i)/A i :=
    Eventually.of_forall fun i => div_nonneg (incidences_nonneg _ _) (hAp i).le
  have hEB0 : ∀ᶠi in filter,0≤ incidences (P i) (Q i)/B i :=
    Eventually.of_forall fun i => div_nonneg (incidences_nonneg _ _) (hBp i).le
  have hPA := hEA.mul hQ hEA0 (Eventually.of_forall fun i => Nat.cast_nonneg _) ht
  have hPB := hP.mul hEB (Eventually.of_forall fun i => Nat.cast_nonneg _) hEB0 ht
  have hPA0 : ∀ᶠi in filter,0≤ incidences (P i) (Q i)/A i*((Q i).card:ℝ) :=
    hEA0.mono fun i hi => mul_nonneg hi (Nat.cast_nonneg _)
  have hPB0 : ∀ᶠi in filter,0≤((P i).card:ℝ)*(incidences (P i) (Q i)/B i) :=
    hEB0.mono fun i hi => mul_nonneg (Nat.cast_nonneg _) hi
  have hMA := (hPA.rpow hPA0 ht (by norm_num : (0:ℝ)<2/3)).exponent_mono
    (show ((2+2*a-(1+b))+(2+a))*(2/3:ℝ)≤2+2*a-b/2 by linarith) ht
  have hMB := (hPB.rpow hPB0 ht (by norm_num : (0:ℝ)<2/3)).exponent_mono
    (show ((1+2*a)+(2+2*a-(a+b)))*(2/3:ℝ)≤2+2*a-b/2 by linarith) ht
  have hSA := (hMA.add (hEA.exponent_mono (by linarith : 2+2*a-(1+b)≤2+2*a-b/2) ht) ht).add
    (hQ.exponent_mono (by linarith : 2+a≤2+2*a-b/2) ht) ht
  have hSB := (hMB.add (hP.exponent_mono (by linarith : 1+2*a≤2+2*a-b/2) ht) ht).add
    (hEB.exponent_mono (by linarith : 2+2*a-(a+b)≤2+2*a-b/2) ht) ht
  have hA0 : ∀ᶠi in filter,0≤(incidences (P i) (Q i)/A i*((Q i).card:ℝ))^(2/3:ℝ)+incidences (P i) (Q i)/A i+(Q i).card := by
    filter_upwards [hEA0] with i hi
    positivity
  have hB0 : ∀ᶠi in filter,0≤(((P i).card:ℝ)*(incidences (P i) (Q i)/B i))^(2/3:ℝ)+(P i).card+incidences (P i) (Q i)/B i := by
    filter_upwards [hEB0] with i hi
    positivity
  have hLA := hLu.mul hSA (Eventually.of_forall fun i => by positivity) hA0 ht
  have hLB := hLu.mul hSB (Eventually.of_forall fun i => by positivity) hB0 ht
  simp only [zero_add] at hLA hLB
  have hloss := hLA.add hLB ht
  have hnon : ∀ᶠi in filter,0≤1000*(L i)^2*((incidences (P i) (Q i)/A i*((Q i).card:ℝ))^(2/3:ℝ)+incidences (P i) (Q i)/A i+(Q i).card)+
      1000*(L i)^2*((((P i).card:ℝ)*(incidences (P i) (Q i)/B i))^(2/3:ℝ)+(P i).card+incidences (P i) (Q i)/B i) := by
    filter_upwards [hA0,hB0] with i hi hj
    positivity
  refine ⟨F,G,fun i => ⟨hF i,hG i⟩,hdF,hdG,
    hP.mono (Eventually.of_forall fun i => Nat.cast_le.mpr (Finset.card_le_card (hF i))),
    hQ.mono (Eventually.of_forall fun i => Nat.cast_le.mpr (Finset.card_le_card (hG i))),?_⟩
  apply hE.of_loss hloss hnon ht (by linarith)
  exact Eventually.of_forall fun i => by simpa only [add_assoc] using he i
end
end PlanarUnitDistances.CuttingAsymptotics

end OAI

namespace PlanarUnitDistances

open Filter OAI.PlanarUnitDistances
open OAI.PlanarUnitDistances.CircleIncidence
open OAI.PlanarUnitDistances.CircleCutting (cuttingLog)
open OAI.PlanarUnitDistances.PowerGrowth OAI.PlanarUnitDistances.CuttingAsymptotics
open OAI.PlanarUnitDistances.GeometricExpansion
noncomputable section

lemma factor_upper_fixed {ι : Type*} {f : Filter ι} {t m n e L : ι → ℝ} {a b g : ℝ}
    (hg : 0≤g)
    (ht : Tendsto t f atTop) (_ha : 0 < a) (_ha1 : a < 1) (hb : 0 < b)
    (hm : Upper f t m (1+2*a)) (hn : Upper f t n (2+a))
    (he : Lower f t e (2+2*a-g)) (hL : Upper f t L 0)
    (hm0 : ∀ᶠi in f,0 ≤ m i) (hn0 : ∀ᶠi in f,0 ≤ n i)
    (hL0 : ∀ᶠi in f,0 ≤ L i) :
    Upper f t (fun i => factor (m i) (n i) (e i) (L i)
      ((t i)^(1+b)) ((t i)^(a+b)) (t i) a) (b+g) := by
  have he0 := he.eventually_pos ht
  have ht0 := eventually_base_pos ht
  have hC : Upper f t (fun i => 1000*(L i)^2) 0 := by
    have h := (hL.mul hL hL0 hL0 ht).const_mul ht (by norm_num : (0:ℝ) ≤ 1000)
    convert h using 1 <;> ring_nf
  have hC0 : ∀ᶠi in f,0 ≤ 1000*(L i)^2 := Eventually.of_forall fun i => by positivity
  have hmn := (hm.mul hn hm0 hn0 ht).rpow (by filter_upwards [hm0,hn0] with i hi hj; positivity)
    ht (by norm_num : (0:ℝ) < 2/3)
  have hmix := (hC.mul hmn hC0 (by filter_upwards [hm0,hn0] with i hi hj; exact Real.rpow_nonneg (mul_nonneg hi hj) _) ht).div he he0 ht
  have h1 : Upper f t (fun i => 1000*(L i)^2*(m i*n i)^(2/3:ℝ)/e i) (b+g) :=
    hmix.exponent_mono (by linarith) ht
  have hna := hn.mul (upper_rpow ht a) hn0
    (by filter_upwards [ht0] with i hi; positivity) ht
  have h2' := (hC.mul hna hC0 (by filter_upwards [hn0,ht0] with i hi hj; positivity) ht).div he he0 ht
  have h2 : Upper f t (fun i => 1000*(L i)^2*n i*(t i)^a/e i) (b+g) := by
    have hh := h2'.exponent_mono (show 0+(2+a+a)-(2+2*a-g) ≤ b+g by linarith) ht
    convert hh using 1; ring_nf
  have hmt := hm.mul (upper_rpow ht 1) hm0 (by filter_upwards [ht0] with i hi; positivity) ht
  have h3' := (hC.mul hmt hC0 (by filter_upwards [hm0,ht0] with i hi hj; positivity) ht).div he he0 ht
  have h3 : Upper f t (fun i => 1000*(L i)^2*m i*t i/e i) (b+g) := by
    have hh := h3'.exponent_mono (show 0+(1+2*a+1)-(2+2*a-g) ≤ b+g by linarith) ht
    simpa only [Real.rpow_one,mul_assoc] using hh
  have h4' := ((upper_rpow ht (1+b)).mul hm (by filter_upwards [ht0] with i hi; positivity) hm0 ht).div he he0 ht
  have h4 : Upper f t (fun i => (t i)^(1+b)*m i/e i) (b+g) := by
    convert h4' using 1; ring
  have h5' := ((upper_rpow ht (a+b)).mul hn (by filter_upwards [ht0] with i hi; positivity) hn0 ht).div he he0 ht
  have h5 : Upper f t (fun i => (t i)^(a+b)*n i/e i) (b+g) := by
    convert h5' using 1; ring
  exact (((((upper_const ht 1).exponent_mono (by linarith : 0≤b+g) ht).add h1 ht).add h2 ht).add h3 ht).add h4 ht |>.add h5 ht

/-- The cutting input counts ordered pairs, with exactly the project's unit-pair convention. -/
theorem orderedPairs_card_eq_incidences (X : Finset Plane) :
    ((orderedPairs X).card : ℝ) = incidences X X := by
  classical
  simp only [orderedPairs, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, Finset.sum_product, incidences, degree_sum, dist_comm]

/-- The actual trimmed Euclidean incidence graph, uniformly for all large real t
and all dense finite configurations of cardinality t³. -/
theorem fixed_initial_rectangle {g : ℝ} (hg : 0 < g) (ha1 : 10000*g ≤ 1/10) :
    let a := 10000*g
    ∀ᶠ t : ℝ in atTop, ∀ X : Finset Plane, (X.card:ℝ) = t^3 →
      t^(4-g) ≤ ((orderedPairs X).card:ℝ) →
      ∃ P ⊆ X, ∃ Q ⊆ X,
        t^(1+2*a-13*g) ≤ (P.card:ℝ) ∧ (P.card:ℝ) ≤ 2*t^(1+2*a) ∧
        t^(2+a-13*g) ≤ (Q.card:ℝ) ∧ (Q.card:ℝ) ≤ t^(2+a) ∧
        t^(2+2*a-3*g) ≤ incidences P Q ∧
        (∀ p ∈ P, degree Q p ≤ t^(1+10*g)) ∧ (∀ q ∈ Q, degree P q ≤ t^(a+10*g)) ∧
        factor P.card Q.card (incidences P Q) (cuttingLog X.card) (t^(1+10*g)) (t^(a+10*g)) t a ≤ t^(20*g) ∧
        (∀ A ⊆ P, ∀ B ⊆ Q,
          let u := (A.card:ℝ)/P.card
          let v := (B.card:ℝ)/Q.card
          let w := incidences A B/incidences P Q
          w ≤ t^(20*g)*((u*v)^(2/3:ℝ)+t^(-a)*v+t^(-1:ℝ)*u) ∧
          w ≤ t^(20*g)*min u v) := by
  let a := 10000*g
  let I := {z : ℝ × Finset Plane // 1 ≤ z.1 ∧ (z.2.card:ℝ)=z.1^3 ∧
    z.1^(4-g) ≤ ((orderedPairs z.2).card:ℝ)}
  let t : I → ℝ := fun i => i.1.1
  let X : I → Finset Plane := fun i => i.1.2
  let f := Filter.comap t atTop
  have ht : Tendsto t f atTop := tendsto_comap
  have ht1 (i : I) : 1≤t i := i.2.1
  have ht0 (i : I) : 0<t i := zero_lt_one.trans_le (ht1 i)
  have hcard (i : I) : ((X i).card:ℝ)=(t i)^3 := i.2.2.1
  have hX0 (i : I) : (X i).Nonempty := by
    apply Finset.card_pos.mp
    apply (Nat.cast_pos (α := ℝ)).mp
    rw [hcard]
    exact pow_pos (ht0 i) _
  have hX : Upper f t (fun i => ((X i).card:ℝ)) 3 := by
    apply (upper_rpow ht 3).mono
    exact Eventually.of_forall fun i => (hcard i).le.trans_eq (Real.rpow_natCast (t i) 3).symm
  have hE : Lower f t (fun i => incidences (X i) (X i)) (4-g) := by
    apply (lower_rpow ht _).mono
    exact Eventually.of_forall fun i => (i.2.2.2).trans_eq (orderedPairs_card_eq_incidences (X i))
  have ha : 0<a := by dsimp [a]; positivity
  have ha' : a<1 := by dsimp [a]; linarith
  obtain ⟨P,Q,hPQ,hPc,hQc,hPu,hQu,hEl⟩ :=
    exists_cut_fixed_deficit X ht ht1 hX0 hX hcard hE (by dsimp [a]; linarith : g<a) ha ha'
  obtain ⟨F,G,hFG,hdF,hdG,hFu,hGu,hFinal⟩ :=
    trim_fixed_deficit ht ht1 hX (fun i => (hPQ i).1) (fun i => (hPQ i).2)
      (by linarith : g<10*g/2) ha ha' (by linarith : 0<10*g)
      (by dsimp [a]; linarith : 10*g<a) hPu hQu hEl
  have hbound : ∀ᶠ i in f, (t i)^(2+2*a-3*g) ≤ incidences (F i) (G i) := by
    simpa only [show 2+2*a-g-2*g=2+2*a-3*g by ring] using hFinal (2*g) (by positivity)
  let L := fun i => cuttingLog (X i).card
  let T := fun i => factor (F i).card (G i).card (incidences (F i) (G i))
    (L i) ((t i)^(1+10*g)) ((t i)^(a+10*g)) (t i) a
  have hTu := factor_upper_fixed hg.le ht ha ha' (show 0<10*g by linarith)
    hFu hGu hFinal (cuttingLog_upper ht hX)
    (Eventually.of_forall fun i => Nat.cast_nonneg _) (Eventually.of_forall fun i => Nat.cast_nonneg _)
    (Eventually.of_forall fun i => zero_le_one.trans (cuttingLog_one_le _))
  have hT : ∀ᶠ i in f, T i ≤ (t i)^(20*g) := by
    have hh := hTu (9*g) (by positivity)
    have he : 10*g+g+9*g=20*g := by ring
    simpa only [he,T,L] using hh
  have hall : ∀ᶠ i in f,
      ∃ F₀ ⊆ X i, ∃ G₀ ⊆ X i,
        (t i)^(1+2*a-13*g) ≤ (F₀.card:ℝ) ∧ (F₀.card:ℝ) ≤ 2*(t i)^(1+2*a) ∧
        (t i)^(2+a-13*g) ≤ (G₀.card:ℝ) ∧ (G₀.card:ℝ) ≤ (t i)^(2+a) ∧
        (t i)^(2+2*a-3*g) ≤ incidences F₀ G₀ ∧
        (∀ p ∈ F₀, degree G₀ p ≤ (t i)^(1+10*g)) ∧
        (∀ q ∈ G₀, degree F₀ q ≤ (t i)^(a+10*g)) ∧
        factor F₀.card G₀.card (incidences F₀ G₀) (L i) ((t i)^(1+10*g)) ((t i)^(a+10*g)) (t i) a ≤ (t i)^(20*g) ∧
        (∀ A ⊆ F₀, ∀ B ⊆ G₀,
          let u := (A.card:ℝ)/F₀.card
          let v := (B.card:ℝ)/G₀.card
          let w := incidences A B/incidences F₀ G₀
          w ≤ (t i)^(20*g)*((u*v)^(2/3:ℝ)+(t i)^(-a)*v+(t i)^(-1:ℝ)*u) ∧
          w ≤ (t i)^(20*g)*min u v) := by
    filter_upwards [hbound,hT] with i hi hTi
    refine ⟨F i,(hFG i).1.trans (hPQ i).1,G i,(hFG i).2.trans (hPQ i).2,?_,
      (Nat.cast_le.mpr (Finset.card_le_card (hFG i).1)).trans (hPc i),?_,
      (Nat.cast_le.mpr (Finset.card_le_card (hFG i).2)).trans (hQc i),hi,hdF i,hdG i,hTi,?_⟩
    · have h := hi.trans (incidence_degree_le (F i) (G i) (hdF i))
      have hd := Real.rpow_pos_of_pos (ht0 i) (1+10*g)
      have hdiv := (div_le_iff₀ hd).mpr h
      rw [← Real.rpow_sub (ht0 i)] at hdiv
      rwa [show 2+2*a-3*g-(1+10*g) = 1+2*a-13*g by ring] at hdiv
    · have h := incidence_degree_le (G i) (F i) (hdG i)
      rw [incidences_comm (G i) (F i)] at h
      have hd := Real.rpow_pos_of_pos (ht0 i) (a+10*g)
      have hdiv := (div_le_iff₀ hd).mpr (hi.trans h)
      rw [← Real.rpow_sub (ht0 i)] at hdiv
      rwa [show 2+2*a-3*g-(a+10*g) = 2+a-13*g by ring] at hdiv
    · intro A hA B hB
      have hed := (Real.rpow_pos_of_pos (ht0 i) _).trans_le hi
      have hAF := cuttingLog_mono (Finset.card_le_card ((hFG i).1.trans (hPQ i).1))
      have hBG := cuttingLog_mono (Finset.card_le_card ((hFG i).2.trans (hPQ i).2))
      have hs := preliminary_bounds (F i) (G i) (a := a) hed (cuttingLog_one_le _) hAF hBG
        (Real.rpow_nonneg (ht0 i).le _) (Real.rpow_nonneg (ht0 i).le _)
        (ht0 i) (hdF i) (hdG i) A hA B hB
      have htPos := ht0 i
      dsimp only at hs ⊢
      constructor
      · exact hs.1.trans (mul_le_mul_of_nonneg_right hTi (by positivity))
      · exact hs.2.1.trans (mul_le_mul_of_nonneg_right hTi (le_min (by positivity) (by positivity)))
  change ∀ᶠ i in Filter.comap t atTop, _ at hall
  filter_upwards [eventually_comap.mp hall, eventually_ge_atTop (1:ℝ)] with b hb hb1
  intro Y hc hDense
  exact hb (⟨(b,Y),hb1,hc,hDense⟩ : I) rfl

end
end PlanarUnitDistances
