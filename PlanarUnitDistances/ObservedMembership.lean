import PlanarUnitDistances.HashedPrediction
import PlanarUnitDistances.EmpiricalCross

namespace OAI.PlanarUnitDistances.ObservedMembership
open Finset Real FiniteLaw HashFeatures Hashing CrossPrediction
open scoped RealInnerProductSpace Classical
noncomputable section
variable {A B C P Q H : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype P] [Fintype Q]
  [Fintype H] [DecidableEq A] [DecidableEq B] [DecidableEq H] [Nonempty C]

/-- A permitted test, chosen before observing the fresh hash. An empty finite
set also represents turning off the test on a center or list event. -/
inductive Query (A B : Type*) where
  | row (a : A)
  | col (b : B)
  | few (s : Finset (A×B)) (hc : s.card ≤ 2)

def accepts : Query A B → A×B → Prop
  | .row a, x => x.1=a
  | .col b, x => x.2=b
  | .few s _, x => x ∈ s

def mapQuery (f : A → C) (g : B → C) : Query A B → Query C C
  | .row a => .row (f a)
  | .col b => .col (g b)
  | .few s hc => .few (s.image (fun z => (f z.1,g z.2))) ((card_image_le).trans hc)

def testVector (U : Query A B) : V A B := WithLp.toLp 2 (fun j => match j,U with
  | .inl a,.row a' => if a=a' then 1 else 0
  | .inr (.inl b),.col b' => if b=b' then 1 else 0
  | .inr (.inr z),.few s _ => if z∈s then 1 else 0
  | _, _ => 0)

theorem represents (U : Query A B) (x : A×B) :
    inner ℝ (vector x 1 1 1) (testVector U) = if accepts U x then 1 else 0 := by
  rw [PiLp.inner_apply]
  cases U <;> simp [testVector,vector,Fintype.sum_sum_type,Pi.single_apply,RCLike.inner_apply,accepts,mul_ite]
  all_goals split_ifs <;> simp_all

theorem norm_test_le (U : Query A B) : ‖testVector U‖ ≤ sqrt 2 := by
  apply (sq_le_sq₀ (norm_nonneg _) (sqrt_nonneg _)).mp
  rw [sq_sqrt (by norm_num : (0:ℝ) ≤ 2),← real_inner_self_eq_norm_sq,PiLp.inner_apply]
  cases U with
  | row a => simp [testVector,Fintype.sum_sum_type]
  | col b => simp [testVector,Fintype.sum_sum_type]
  | few s hc =>
    simpa [testVector,Fintype.sum_sum_type,RCLike.inner_apply] using (Nat.cast_le.mpr hc : (s.card:ℝ) ≤ 2)

private theorem joint_collision (x y : A×B) (hne : x ≠ y) :
    event (law : Law (Hash A B C)) (fun u => state u x=state u y) ≤ (Fintype.card C:ℝ)⁻¹ := by
  by_cases hx : x.1=y.1
  · have hy : x.2≠y.2 := fun hh => hne (Prod.ext hx hh)
    have b := event_mono (law : Law (Hash A B C)) (P := fun u => state u x=state u y)
      (Q := fun u => u.2 x.2=u.2 y.2) (fun _ h => congrArg Prod.snd h)
    refine b.trans_eq ?_
    change avg (pair (uniform (A → C)) (uniform (B → C))) (fun u => if u.2 x.2=u.2 y.2 then 1 else 0) = _
    rw [pair_snd (uniform (A → C)) (uniform (B → C)) (fun u => if u x.2=u y.2 then 1 else 0),avg_ite]
    exact uniform_collision _ _ hy
  · have b := event_mono (law : Law (Hash A B C)) (P := fun u => state u x=state u y)
      (Q := fun u => u.1 x.1=u.1 y.1) (fun _ h => congrArg Prod.fst h)
    refine b.trans_eq ?_
    change avg (pair (uniform (A → C)) (uniform (B → C))) (fun u => if u.1 x.1=u.1 y.1 then 1 else 0) = _
    rw [pair_fst (uniform (A → C)) (uniform (B → C)) (fun u => if u x.1=u y.1 then 1 else 0),avg_ite]
    exact uniform_collision _ _ hx

def ind (U : Query A B) (x : A×B) : ℝ := if accepts U x then 1 else 0

theorem hash_membership_error (U : Query A B) (x : A×B) :
    |avg (law : Law (Hash A B C)) (fun u => ind (mapQuery u.1 u.2 U) (state u x)) - ind U x| ≤
      2/(Fintype.card C:ℝ) := by
  have nn : 0 ≤ (Fintype.card C:ℝ)⁻¹ := by positivity
  by_cases hx : accepts U x
  · have eqv (u : Hash A B C) : ind (mapQuery u.1 u.2 U) (state u x) = 1 := by
      apply if_pos
      cases U with
      | row a => exact congrArg u.1 hx
      | col b => exact congrArg u.2 hx
      | few s hc => exact mem_image_of_mem _ hx
    have avgEq := avg_congr (law : Law (Hash A B C)) eqv
    rw [avgEq,avg_const,show ind U x = 1 from if_pos hx,sub_self,abs_zero]
    positivity
  have zero : ind U x=0 := if_neg hx
  have pp : 0 ≤ avg (law : Law (Hash A B C)) (fun u => ind (mapQuery u.1 u.2 U) (state u x)) :=
    avg_nonneg _ (fun _ => by unfold ind; split <;> norm_num)
  rw [zero,sub_zero,abs_of_nonneg pp]
  cases U with
  | row a =>
    have hu : event (uniform (A → C)) (fun f => f x.1=f a) = _ := uniform_collision x.1 a hx
    change avg (pair (uniform (A → C)) (uniform (B → C))) (fun u => if u.1 x.1=u.1 a then 1 else 0) ≤ _
    rw [pair_fst (uniform (A → C)) (uniform (B → C)) (fun f => if f x.1=f a then 1 else 0),avg_ite,hu]
    rw [div_eq_mul_inv]; linarith
  | col b =>
    have hu : event (uniform (B → C)) (fun f => f x.2=f b) = _ := uniform_collision x.2 b hx
    change avg (pair (uniform (A → C)) (uniform (B → C))) (fun u => if u.2 x.2=u.2 b then 1 else 0) ≤ _
    rw [pair_snd (uniform (A → C)) (uniform (B → C)) (fun f => if f x.2=f b then 1 else 0),avg_ite,hu]
    rw [div_eq_mul_inv]; linarith
  | few s hs =>
    let hit (y : A×B) (u : Hash A B C) := state u x=state u y
    have term (u : Hash A B C) : ind (mapQuery u.1 u.2 (.few s hs)) (state u x) ≤ ∑ y ∈ s, if hit y u then 1 else 0 := by
      unfold ind
      split_ifs with hy
      · obtain ⟨z,hz,he⟩ := mem_image.mp hy
        have equal : hit z u := he.symm
        exact (show (1:ℝ) = (if hit z u then 1 else 0) by simp [equal]).trans_le
          (single_le_sum (s := s) (f := fun y => if hit y u then (1:ℝ) else 0) (fun y _ => by split <;> norm_num) hz)
      · positivity
    refine (avg_mono _ term).trans ?_
    have ex : avg (law : Law (Hash A B C)) (fun u => ∑ y ∈ s, if hit y u then 1 else 0) =
        ∑ y ∈ s, event (law : Law (Hash A B C)) (hit y) := by
      unfold event avg
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro y _
      apply sum_congr rfl
      intro u _
      by_cases hh : hit y u <;> simp [hh]
    rw [ex]
    calc
      _ ≤ ∑ _y ∈ s, (Fintype.card C:ℝ)⁻¹ :=
        sum_le_sum fun y hy => joint_collision x y (fun eq => hx (eq ▸ hy))
      _ ≤ 2/(Fintype.card C:ℝ) := by
        simp only [Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv]
        gcongr; exact_mod_cast hs

end
end OAI.PlanarUnitDistances.ObservedMembership

namespace OAI.PlanarUnitDistances.ObservedMembership
open Finset Real FiniteLaw HashFeatures Hashing CrossPrediction
open scoped RealInnerProductSpace Classical
noncomputable section
variable {P Q A B H C : Type*} [Fintype P] [Fintype Q] [Fintype A] [Fintype B]
  [Fintype C] [Fintype H] [DecidableEq H] [DecidableEq A] [DecidableEq B] [Nonempty C]


/-- A center-dependent random query. The auxiliary list is independent of
the tested neighbor and of the fresh hashes, conditional on the center. -/
theorem transfer_list {L Θ : Type*} [Fintype L] [Nonempty L] [Fintype Θ]
    (κ : Law Q) (w : Q → Law P) (hp : ∀ p, 0 < (mixture κ w).val p) (h : P → H)
    (x : P → A×B) (a : Q → Law Θ) (query : Q → Θ → Query A B) :
    let tr := avg κ (fun q => avg (a q) (fun θ => avg (w q) (fun p => ind (query q θ) (x p))))
    let pr := avg κ (fun q => avg (a q) (fun θ => avg (w q) (fun p =>
      avg (cond (mixture κ w) h (h p)) (fun r => ind (query q θ) (x r)))))
    |tr-pr| ≤ 4/(Fintype.card L:ℝ) + sqrt 2 * hashNorm (C := L) κ w h x := by
  classical
  let hash : Law (Hash A B L) := law
  let trueAt (x' : P → L×L) (u : Hash A B L) := avg κ (fun q => avg (a q) (fun θ =>
    avg (w q) (fun p => ind (mapQuery u.1 u.2 (query q θ)) (x' p))))
  let predAt (x' : P → L×L) (u : Hash A B L) := avg κ (fun q => avg (a q) (fun θ =>
    avg (w q) (fun p => avg (cond (mixture κ w) h (h p)) (fun r => ind (mapQuery u.1 u.2 (query q θ)) (x' r)))))
  let tr (u : Hash A B L) := trueAt (state u ∘ x) u
  let pr (u : Hash A B L) := predAt (state u ∘ x) u
  let tr0 := avg κ (fun q => avg (a q) (fun θ => avg (w q) (fun p => ind (query q θ) (x p))))
  let pr0 := avg κ (fun q => avg (a q) (fun θ => avg (w q) (fun p =>
    avg (cond (mixture κ w) h (h p)) (fun r => ind (query q θ) (x r)))))
  change |tr0-pr0| ≤ _
  have td : |avg hash tr-tr0| ≤ 2/(Fintype.card L:ℝ) := by
    unfold tr trueAt tr0
    rw [avg_comm]
    simp_rw [avg_comm hash]
    exact abs_avg_sub_le _ (fun q => abs_avg_sub_le _ (fun θ => abs_avg_sub_le _
      (fun p => hash_membership_error (query q θ) (x p))))
  have pd : |avg hash pr-pr0| ≤ 2/(Fintype.card L:ℝ) := by
    unfold pr predAt pr0
    rw [avg_comm]
    simp_rw [avg_comm hash]
    exact abs_avg_sub_le _ (fun q => abs_avg_sub_le _ (fun θ => abs_avg_sub_le _
      (fun p => abs_avg_sub_le _ (fun r => hash_membership_error (query q θ) (x r)))))
  have hm : FiniteInformation.marginal κ.val (fun q => (w q).val) = (mixture κ w).val := rfl
  have middle (u : Hash A B L) : |tr u-pr u| ≤ sqrt 2 * FiniteInformation.predictionNorm κ.val
      (fun q => (w q).val) h (state u ∘ x) (fun c => vector c 1 1 1) := by
    let f q θ := testVector (mapQuery u.1 u.2 (query q θ))
    let g (q : Q) := ∑ θ, (a q).val θ • f q θ
    have gg (q : Q) : ‖g q‖ ≤ sqrt 2 := calc
      _ ≤ ∑ θ, ‖(a q).val θ • f q θ‖ := norm_sum_le _ _
      _ ≤ ∑ θ, (a q).val θ * sqrt 2 := sum_le_sum fun θ _ => by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ((a q).nonneg θ)]
        exact mul_le_mul_of_nonneg_left (norm_test_le _) ((a q).nonneg θ)
      _ = _ := by rw [← sum_mul,(a q).total,one_mul]
    apply le_trans _ (discrepancy_norm_bound κ w h (state u ∘ x) (fun c => vector c 1 1 1) g gg)
    apply le_of_eq
    unfold FiniteInformation.testDiscrepancy
    rw [hm]
    simp_rw [FiniteInformation.mean_posterior,posterior_cond _ _ _ (hp _),sum_inner,real_inner_smul_left,
      inner_sub_left,sum_inner,real_inner_smul_left]
    simp only [g,inner_sum,real_inner_smul_right,f,represents,tr,pr,trueAt,predAt,avg,ind]
    congr 1
    simp only [mul_sub,sum_sub_distrib,mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro q _
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro θ _
      ring
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro θ _
      ring
  have mid : |avg hash tr-avg hash pr| ≤ sqrt 2*hashNorm (C := L) κ w h x := by
    rw [←avg_sub,hashNorm,←avg_smul]
    exact (abs_avg_le hash _).trans (avg_mono hash middle)
  simp only [div_eq_mul_inv] at td pd ⊢
  rw [abs_le]
  constructor <;> linarith only [(abs_le.mp td).1,(abs_le.mp td).2,(abs_le.mp pd).1,
    (abs_le.mp pd).2,(abs_le.mp mid).1,(abs_le.mp mid).2]


def rejectChance {Θ : Type*} [Fintype Θ]
    (κ : Law Q) (w : Q → Law P) (x : P → A×B) (a : Q → Law Θ)
    (active : Q → Θ → Prop) (query : Q → Θ → Query A B) : ℝ :=
  avg κ (fun q => avg (a q) (fun θ => event (w q) (fun p =>
    active q θ ∧ ¬accepts (query q θ) (x p))))

/-- The observational transfer, retaining the tested event as well as the random query. -/
theorem reject_bound {L Θ : Type*} [Fintype L] [Nonempty L] [Fintype Θ]
    (κ : Law Q) (w : Q → Law P) (hp : ∀ p, 0 < (mixture κ w).val p) (h : P → H)
    (x : P → A×B) (a : Q → Law Θ) (active : Q → Θ → Prop) (query : Q → Θ → Query A B)
    {b : ℝ} (hb : 0 ≤ b)
    (hbad : ∀ q θ, active q θ → avg (w q) (fun p => event (cond (mixture κ w) h (h p))
      (fun r => ¬accepts (query q θ) (x r))) ≤ b) :
    rejectChance κ w x a active query ≤ b + 4/(Fintype.card L:ℝ) + sqrt 2 * hashNorm (C := L) κ w h x := by
  let test (q : Q) (θ : Θ) : Query A B := if active q θ then query q θ else .few ∅ (by simp)
  let c (q : Q) (θ : Θ) : ℝ := if active q θ then 1 else 0
  have point (q : Q) (θ : Θ) (r : P) :
      (if active q θ ∧ ¬accepts (query q θ) (x r) then (1:ℝ) else 0)
      = c q θ - ind (test q θ) (x r) := by
    by_cases t : active q θ
    · by_cases u : accepts (query q θ) (x r) <;> simp [c,test,ind,t,u]
    · simp [c,test,ind,t,accepts]
  have rej (q : Q) (θ : Θ) (wᵣ : Law P) : event wᵣ (fun r => active q θ ∧ ¬accepts (query q θ) (x r))
      = c q θ - avg wᵣ (fun r => ind (test q θ) (x r)) := by
    rw [← avg_ite wᵣ (fun r => active q θ ∧ ¬accepts (query q θ) (x r))]
    exact (avg_congr wᵣ (point q θ)).trans (by rw [avg_sub,avg_const])
  have pred (q : Q) (θ : Θ) : avg (w q) (fun p => event (cond (mixture κ w) h (h p))
      (fun r => active q θ ∧ ¬accepts (query q θ) (x r))) ≤ b := by
    by_cases ht : active q θ
    · simpa only [ht,true_and] using hbad q θ ht
    · simpa [ht,event,avg_const] using hb
  have hh := (abs_le.mp (transfer_list (L := L) κ w hp h x a test)).1
  have bd := avg_le_const κ (fun q => avg_le_const (a q) (pred q))
  unfold rejectChance
  simp_rw [rej] at bd ⊢
  simp only [avg_sub,avg_const] at bd ⊢
  linarith

end
end OAI.PlanarUnitDistances.ObservedMembership

namespace OAI.PlanarUnitDistances.ObservedMembership
open Finset Real FiniteLaw CrossPrediction MeasureTheory
open scoped Classical
noncomputable section
variable {P Q A B : Type*} [Fintype P] [Fintype Q] [Fintype A] [Fintype B]

end
end OAI.PlanarUnitDistances.ObservedMembership
