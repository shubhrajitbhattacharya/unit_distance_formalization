/- Adapted from OpenAI math, UnitDistances/Powers.lean and Regularization.lean,
   commit adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0). -/
import PlanarUnitDistances.CircleSampling

namespace OAI
namespace PlanarUnitDistances.CircleIncidence
open Finset CircleCutting
open scoped Classical
noncomputable section

lemma high_degree_card (P Q : Finset Plane) {a : ℝ} (ha : 0 < a) :
    ((Q.filter (fun q => a < degree P q)).card : ℝ) ≤ incidences P Q/a := by
  apply (le_div_iff₀ ha).mpr
  have hh : ((Q.filter (fun q => a < degree P q)).card : ℝ)*a ≤ ∑q ∈ Q.filter (fun q => a < degree P q),degree P q := by
    calc
      _ = ∑q ∈ Q.filter (fun q => a < degree P q),a := by simp
      _ ≤ _ := Finset.sum_le_sum (fun q hq => (Finset.mem_filter.mp hq).2.le)
  exact hh.trans (incidences_mono_right P (Finset.filter_subset _ _))

lemma incidence_bound_enlarged (P Q : Finset Plane) {L m n : ℝ}
    (hL : 1 ≤ L) (hlP : cuttingLog P.card ≤ L) (hlQ : cuttingLog Q.card ≤ L)
    (hm : (P.card : ℝ) ≤ m) (hn : (Q.card : ℝ) ≤ n) :
    incidences P Q ≤ 1000*L^2*((m*n)^((2:ℝ)/3)+m+n) := by
  have h0 := (Nat.cast_nonneg P.card : (0:ℝ) ≤ P.card)
  have h1 := (Nat.cast_nonneg Q.card : (0:ℝ) ≤ Q.card)
  have hi : incidences P Q ≤ 1000*L^2*(((P.card:ℝ)*Q.card)^((2:ℝ)/3)+P.card+Q.card) := by
    rcases le_total P.card Q.card with h | h
    · exact incidence_bound_oriented P Q h hL hlQ
    · have he := incidence_bound_oriented Q P h hL hlP
      rw [incidences_comm Q P] at he
      convert he using 1; ring_nf
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hp := Real.rpow_le_rpow (mul_nonneg h0 h1)
    (mul_le_mul hm hn h1 (h0.trans hm)) (by norm_num : (0:ℝ) ≤ 2/3)
  linarith

theorem exists_trimmed (P Q : Finset Plane) {a b L : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hL : 1 ≤ L)
    (hlP : cuttingLog P.card ≤ L) (hlQ : cuttingLog Q.card ≤ L) :
    ∃F ⊆ P,∃G ⊆ Q,
      (∀p∈F,degree G p ≤ a) ∧ (∀q∈G,degree F q ≤ b) ∧
      incidences P Q ≤ incidences F G+
        1000*L^2*((incidences P Q/a*(Q.card:ℝ))^((2:ℝ)/3)+incidences P Q/a+Q.card)+
        1000*L^2*(((P.card:ℝ)*(incidences P Q/b))^((2:ℝ)/3)+P.card+incidences P Q/b) := by
  let F := P.filter (fun p => degree Q p ≤ a)
  let G := Q.filter (fun q => degree P q ≤ b)
  let H := P.filter (fun p => a < degree Q p)
  let J := Q.filter (fun q => b < degree P q)
  have hF : F⊆P := Finset.filter_subset _ _
  have hG : G⊆Q := Finset.filter_subset _ _
  have hH : H⊆P := Finset.filter_subset _ _
  have hJ : J⊆Q := Finset.filter_subset _ _
  have hcH : (H.card:ℝ) ≤ incidences P Q/a := by
    simpa only [incidences_comm Q P] using high_degree_card Q P ha
  have hcJ : (J.card:ℝ) ≤ incidences P Q/b := high_degree_card P Q hb
  have hHP : cuttingLog H.card ≤ L := (cuttingLog_mono (Finset.card_le_card hH)).trans hlP
  have hJQ : cuttingLog J.card ≤ L := (cuttingLog_mono (Finset.card_le_card hJ)).trans hlQ
  have heH := incidence_bound_enlarged H Q hL hHP hlQ hcH (le_refl (Q.card:ℝ))
  have heJ := incidence_bound_enlarged P J hL hlP hJQ (le_refl (P.card:ℝ)) hcJ
  have hs1 : incidences P Q=incidences F Q+incidences H Q := by
    simpa only [not_le] using incidences_filter_split P Q (fun p => degree Q p ≤ a)
  have hs2 : incidences F Q=incidences F G+incidences F J := by
    have hh := incidences_filter_split Q F (fun q => degree P q ≤ b)
    have hh' : incidences Q F=incidences G F+incidences J F := by
      simpa only [not_le] using hh
    simpa only [incidences_comm Q F,incidences_comm G F,incidences_comm J F] using hh'
  have hfj := incidences_mono_left hF J
  refine ⟨F,hF,G,hG,?_,?_,?_⟩
  · intro p hp
    exact (degree_mono hG p).trans (Finset.mem_filter.mp hp).2
  · intro q hq
    exact (degree_mono hF q).trans (Finset.mem_filter.mp hq).2
  · linarith
end
end PlanarUnitDistances.CircleIncidence

namespace PlanarUnitDistances.IncidenceRegularization
open Finset Real

noncomputable def mass {A : Type*} (μ : A → ℝ) (s : Finset A) : ℝ := ∑ a ∈ s, μ a
noncomputable def rect {P Q : Type*} (w : P → Q → ℝ)
    (F : Finset P) (G : Finset Q) : ℝ := ∑ p ∈ F, ∑ q ∈ G, w p q

lemma mass_nonneg {A : Type*} (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (s : Finset A) :
    0 ≤ mass μ s := sum_nonneg (fun a _ => hμ a)
lemma mass_mono {A : Type*} (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    {s t : Finset A} (hst : s ⊆ t) : mass μ s ≤ mass μ t :=
  sum_le_sum_of_subset_of_nonneg hst (fun a _ _ => hμ a)

section Optimizer
variable {P Q : Type*} [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q]
variable (μ : P → ℝ) (ν : Q → ℝ) (w : P → Q → ℝ)

noncomputable def objective (γ : ℝ) (F : Finset P) (G : Finset Q) : ℝ :=
  rect w F G / (mass μ F * mass ν G)^γ

def IsMaximizing (τ γ : ℝ) (F : Finset P) (G : Finset Q) : Prop :=
  τ ≤ mass μ F ∧ τ ≤ mass ν G ∧
    ∀ A B, τ ≤ mass μ A → τ ≤ mass ν B →
      objective μ ν w γ A B ≤ objective μ ν w γ F G

omit [DecidableEq P] [DecidableEq Q] in

theorem exists_maximizing {τ γ : ℝ} (hτ : τ ≤ 1)
    (hμ : ∑ p, μ p = 1) (hν : ∑ q, ν q = 1)
    (hw : ∑ p, ∑ q, w p q = 1) :
    ∃ F G, IsMaximizing μ ν w τ γ F G ∧ 1 ≤ objective μ ν w γ F G := by
  classical
  let S : Finset (Finset P × Finset Q) := univ.filter fun x =>
    τ ≤ mass μ x.1 ∧ τ ≤ mass ν x.2
  have hfull : ((univ : Finset P), (univ : Finset Q)) ∈ S := by
    apply mem_filter.mpr
    exact ⟨mem_univ _, by simpa [mass,hμ,hν] using And.intro hτ hτ⟩
  obtain ⟨⟨F,G⟩,hFG,hmax⟩ := S.exists_max_image
    (fun x => objective μ ν w γ x.1 x.2) ⟨_,hfull⟩
  have hfeas := (mem_filter.mp hFG).2
  refine ⟨F,G,⟨hfeas.1,hfeas.2,?_⟩,?_⟩
  · intro A B hA hB
    exact hmax (A,B) (by simp [S,hA,hB])
  · have hh := hmax (univ,univ) hfull
    simpa [objective, mass, rect, hμ, hν, hw] using hh

omit [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q] in
lemma winner_positive {τ γ : ℝ} {F : Finset P} {G : Finset Q}
    (hτ : 0 < τ) (hmax : IsMaximizing μ ν w τ γ F G)
    (hwin : 1 ≤ objective μ ν w γ F G) :
    0 < mass μ F ∧ 0 < mass ν G ∧ 0 < rect w F G ∧
      (mass μ F * mass ν G)^γ ≤ rect w F G := by
  have hU := hτ.trans_le hmax.1
  have hV := hτ.trans_le hmax.2.1
  have hpow := rpow_pos_of_pos (mul_pos hU hV) γ
  have hW : (mass μ F * mass ν G)^γ ≤ rect w F G := by
    simpa using (le_div_iff₀ hpow).mp hwin
  exact ⟨hU,hV,hpow.trans_le hW,hW⟩

omit [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q] in

theorem feasible_expansion {τ γ : ℝ} {F : Finset P} {G : Finset Q}
    (hτ : 0 < τ) (hmax : IsMaximizing μ ν w τ γ F G)
    (hW : 0 < rect w F G) (A : Finset P) (B : Finset Q)
    (hA : τ ≤ mass μ A) (hB : τ ≤ mass ν B) :
    rect w A B / rect w F G ≤
      (mass μ A / mass μ F * (mass ν B / mass ν G))^γ := by
  have hU := hτ.trans_le hmax.1
  have hV := hτ.trans_le hmax.2.1
  have hα := hτ.trans_le hA
  have hβ := hτ.trans_le hB
  have hUV := rpow_pos_of_pos (mul_pos hU hV) γ
  have hαβ := rpow_pos_of_pos (mul_pos hα hβ) γ
  have ho := hmax.2.2 A B hA hB
  unfold objective at ho
  have ho' := (div_le_div_iff₀ hαβ hUV).mp ho
  have hid : mass μ A / mass μ F * (mass ν B / mass ν G) =
      (mass μ A * mass ν B)/(mass μ F * mass ν G) := by ring
  rw [hid, div_rpow (mul_pos hα hβ).le (mul_pos hU hV).le]
  exact (div_le_div_iff₀ hW hUV).mpr (by nlinarith)

omit [Fintype P] [Fintype Q] [DecidableEq Q] in

theorem left_atom_bound {τ γ : ℝ} (_hμ : ∀ p, 0 ≤ μ p)
    {F : Finset P} {G : Finset Q} (hτ : 0 < τ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hmax : IsMaximizing μ ν w τ γ F G) (hW : 0 < rect w F G)
    {p : P} (hp : p ∈ F) (herase : τ ≤ mass μ (F.erase p)) :
    γ * (μ p / mass μ F) ≤ (∑ q ∈ G, w p q) / rect w F G := by
  have hU := hτ.trans_le hmax.1
  have hV := hτ.trans_le hmax.2.1
  have hsum : mass μ (F.erase p) + μ p = mass μ F := by
    exact sum_erase_add _ _ hp
  have hrect : rect w (F.erase p) G + (∑ q ∈ G, w p q) = rect w F G := by
    exact sum_erase_add _ _ hp
  have he := feasible_expansion μ ν w hτ hmax hW (F.erase p) G herase hmax.2.1
  have hratio : mass μ (F.erase p) / mass μ F = 1 - μ p / mass μ F := by
    apply (div_eq_iff hU.ne').mpr
    field_simp
    linarith
  rw [div_self hV.ne', mul_one, hratio] at he
  have hple : μ p ≤ mass μ F := by linarith [mass_nonneg μ _hμ (F.erase p)]
  have hratio1 : μ p / mass μ F ≤ 1 := (div_le_one hU).mpr hple
  have hBern := rpow_one_add_le_one_add_mul_self
    (by linarith : -1 ≤ -(μ p / mass μ F)) hγ hγ1
  have hBern' : (1 - μ p / mass μ F)^γ ≤ 1-γ*(μ p / mass μ F) := by
    simpa only [sub_eq_add_neg, mul_neg] using hBern
  have he' := he.trans hBern'
  have hd : rect w (F.erase p) G / rect w F G +
      (∑ q ∈ G, w p q) / rect w F G = 1 := by
    rw [← add_div, hrect, div_self hW.ne']
  linarith

omit [DecidableEq P] in
lemma mass_le_one (hμ : ∀ p, 0 ≤ μ p) (hs : ∑ p, μ p = 1) (F : Finset P) :
    mass μ F ≤ 1 := by
  simpa [mass,hs] using mass_mono μ hμ (subset_univ F)

omit [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q] in
lemma transpose_maximizing {τ γ : ℝ} {F : Finset P} {G : Finset Q}
    (hm : IsMaximizing μ ν w τ γ F G) :
    IsMaximizing ν μ (fun q p => w p q) τ γ G F := by
  refine ⟨hm.2.1,hm.1,?_⟩
  intro B A hB hA
  have hh := hm.2.2 A B hA hB
  have hrect (A : Finset P) (B : Finset Q) :
      rect (fun q p => w p q) B A = rect w A B := sum_comm
  simpa only [objective, hrect, mul_comm] using hh

omit [Fintype P] [Fintype Q] [DecidableEq P] in
theorem right_atom_bound {τ γ : ℝ} (hν : ∀ q, 0 ≤ ν q)
    {F : Finset P} {G : Finset Q} (hτ : 0 < τ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hmax : IsMaximizing μ ν w τ γ F G) (hW : 0 < rect w F G)
    {q : Q} (hq : q ∈ G) (herase : τ ≤ mass ν (G.erase q)) :
    γ * (ν q / mass ν G) ≤ (∑ p ∈ F, w p q) / rect w F G := by
  have ht : rect (fun q p => w p q) G F = rect w F G := sum_comm
  have he := left_atom_bound ν μ (fun q p => w p q) hν hτ hγ hγ1
    (transpose_maximizing μ ν w hmax) (by rw [ht]; exact hW) hq herase
  simpa only [ht] using he

end Optimizer

lemma min_le_geometric {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min x y ≤ sqrt (x*y) := by
  have hh : (min x y)^2 ≤ x*y := by
    rcases le_total x y with h|h
    · rw [min_eq_left h]
      nlinarith [mul_nonneg hx (sub_nonneg.mpr h)]
    · rw [min_eq_right h]
      nlinarith [mul_nonneg hy (sub_nonneg.mpr h)]
  have hs := sq_sqrt (mul_nonneg hx hy)
  have hn := sqrt_nonneg (x*y)
  nlinarith [min_le_left x y, min_le_right x y]

theorem preliminary_square_root {u v a b T w : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (ha : 0 ≤ a) (hb : 0 ≤ b) (hT : 0 ≤ T)
    (hi : w ≤ T*((u*v)^((2:ℝ)/3)+a*v+b*u))
    (hdP : w ≤ T*u) (hdQ : w ≤ T*v) :
    w ≤ T*sqrt (u*v)*((u*v)^((1:ℝ)/6)+sqrt a+sqrt b) := by
  have hA := rpow_nonneg (mul_nonneg hu hv) ((2:ℝ)/3)
  have hc : w ≤ T*((u*v)^((2:ℝ)/3)+min (a*v) u+min (b*u) v) := by
    by_cases h1 : a*v ≤ u
    · rw [min_eq_left h1]
      by_cases h2 : b*u ≤ v
      · simpa only [min_eq_left h2] using hi
      · rw [min_eq_right (le_of_not_ge h2)]
        exact hdQ.trans (mul_le_mul_of_nonneg_left (by nlinarith) hT)
    · rw [min_eq_right (le_of_not_ge h1)]
      exact hdP.trans (mul_le_mul_of_nonneg_left
        (by linarith [le_min (mul_nonneg hb hu) hv]) hT)
  have hz1 : min (a*v) u ≤ sqrt a * sqrt (u*v) := by
    have := min_le_geometric (mul_nonneg ha hv) hu
    convert this using 1
    rw [← sqrt_mul ha]
    congr 1
    ring
  have hz2 : min (b*u) v ≤ sqrt b * sqrt (u*v) := by
    have := min_le_geometric (mul_nonneg hb hu) hv
    convert this using 1
    rw [← sqrt_mul hb]
    congr 1
    ring
  have hpow : (u*v)^((2:ℝ)/3) = sqrt (u*v)*(u*v)^((1:ℝ)/6) := by
    by_cases hzero : u*v = 0
    · simp [hzero, zero_rpow (by norm_num : (2:ℝ)/3 ≠ 0)]
    · rw [sqrt_eq_rpow, ← rpow_add (lt_of_le_of_ne (mul_nonneg hu hv) (Ne.symm hzero))]
      norm_num
  calc
    w ≤ T*((u*v)^((2:ℝ)/3)+min (a*v) u+min (b*u) v) := hc
    _ ≤ T*((u*v)^((2:ℝ)/3)+sqrt a*sqrt (u*v)+sqrt b*sqrt (u*v)) :=
      mul_le_mul_of_nonneg_left (by linarith) hT
    _ = T*sqrt (u*v)*((u*v)^((1:ℝ)/6)+sqrt a+sqrt b) := by rw [hpow]; ring

lemma renormalized_preliminary {α β U V W T ρ e x : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hU : 0 < U) (hV : 0 < V)
    (hU1 : U ≤ 1) (hV1 : V ≤ 1) (hW : 0 < W)
    (hT : 0 ≤ T) (hρ : 0 ≤ ρ)
    (hp : x ≤ T*sqrt (α*β)*((α*β)^ρ+e)) :
    x/W ≤ (T*sqrt (U*V)/W)*sqrt (α/U*(β/V))*
      ((α/U*(β/V))^ρ+e) := by
  have hUV : 0 < U*V := mul_pos hU hV
  have huv : 0 ≤ α/U*(β/V) := mul_nonneg (div_nonneg hα hU.le) (div_nonneg hβ hV.le)
  have hid : α*β = (U*V)*(α/U*(β/V)) := by field_simp
  have hUV1 : U*V ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hU1) (sub_nonneg.mpr hV1)]
  have hle : α*β ≤ α/U*(β/V) := by rw [hid]; nlinarith
  have hr := rpow_le_rpow (mul_nonneg hα hβ) hle hρ
  have hrt : 0 ≤ T*sqrt (α*β) := mul_nonneg hT (sqrt_nonneg _)
  have hb := hp.trans (mul_le_mul_of_nonneg_left (show (α*β)^ρ+e ≤ (α/U*(β/V))^ρ+e by linarith) hrt)
  have hs : sqrt (α*β) = sqrt (U*V)*sqrt (α/U*(β/V)) := by
    rw [hid, sqrt_mul hUV.le]
  apply (div_le_iff₀ hW).mpr
  have heq : (T*sqrt (U*V)/W)*sqrt (α/U*(β/V))*
      ((α/U*(β/V))^ρ+e)*W = T*(sqrt (U*V)*sqrt (α/U*(β/V)))*
      ((α/U*(β/V))^ρ+e) := by field_simp
  rw [heq]
  simpa [hs] using hb

theorem maximizing_expansion {P Q : Type*} [Fintype P] [Fintype Q]
    [DecidableEq P] [DecidableEq Q]
    (μ : P → ℝ) (ν : Q → ℝ) (w : P → Q → ℝ)
    (hμ : ∀ p, 0 ≤ μ p) (hν : ∀ q, 0 ≤ ν q)
    (hμs : ∑ p, μ p = 1) (hνs : ∑ q, ν q = 1)
    {τ η ρ T e : ℝ} (hτ : 0 < τ) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hT : 0 ≤ T) (he : 0 ≤ e)
    {F : Finset P} {G : Finset Q}
    (hm : IsMaximizing μ ν w τ ((1:ℝ)/2+η) F G)
    (hW : 0 < rect w F G)
    (hpre : ∀ A B, rect w A B ≤
      T*sqrt (mass μ A * mass ν B)*((mass μ A * mass ν B)^ρ+e)) :
    let ξ := (T*sqrt (mass μ F * mass ν G)/rect w F G)*
      ((τ/min (mass μ F) (mass ν G))^ρ+e)
    ∀ A ⊆ F, ∀ B ⊆ G,
      rect w A B/rect w F G ≤
        sqrt (mass μ A/mass μ F*(mass ν B/mass ν G))*
          ((mass μ A/mass μ F*(mass ν B/mass ν G))^η+ξ) := by
  dsimp only
  intro A hAF B hBG
  let U := mass μ F
  let V := mass ν G
  let α := mass μ A
  let β := mass ν B
  let W := rect w F G
  let u := α/U
  let v := β/V
  let C := T*sqrt (U*V)/W
  let ξ := C*((τ/min U V)^ρ+e)
  have hU : 0 < U := hτ.trans_le hm.1
  have hV : 0 < V := hτ.trans_le hm.2.1
  have hU1 : U ≤ 1 := mass_le_one μ hμ hμs F
  have hV1 : V ≤ 1 := mass_le_one ν hν hνs G
  have hα : 0 ≤ α := mass_nonneg μ hμ A
  have hβ : 0 ≤ β := mass_nonneg ν hν B
  have hαU : α ≤ U := mass_mono μ hμ hAF
  have hβV : β ≤ V := mass_mono ν hν hBG
  have hu : 0 ≤ u := div_nonneg hα hU.le
  have hv : 0 ≤ v := div_nonneg hβ hV.le
  have hu1 : u ≤ 1 := (div_le_one hU).mpr hαU
  have hv1 : v ≤ 1 := (div_le_one hV).mpr hβV
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hT (sqrt_nonneg _)) hW.le
  have hmin : 0 < min U V := lt_min hU hV
  have hξ : 0 ≤ ξ := mul_nonneg hC (add_nonneg (rpow_nonneg
    (div_nonneg hτ.le hmin.le) ρ) he)
  have hsplit : (u*v)^((1:ℝ)/2+η) = sqrt (u*v)*(u*v)^η := by
    rw [sqrt_eq_rpow, ← rpow_add' (mul_nonneg hu hv) (by linarith : (1:ℝ)/2+η ≠ 0)]
  change rect w A B/W ≤ sqrt (u*v)*((u*v)^η+ξ)
  by_cases hfeas : τ ≤ α ∧ τ ≤ β
  · have hh := feasible_expansion μ ν w hτ hm hW A B hfeas.1 hfeas.2
    change rect w A B/W ≤ (u*v)^((1:ℝ)/2+η) at hh
    rw [hsplit] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith) (sqrt_nonneg _))
  · have hsmall : u*v ≤ τ/min U V := by
      by_cases ha : τ ≤ α
      · have hb : β < τ := lt_of_not_ge (fun hb => hfeas ⟨ha,hb⟩)
        have hvτ : v ≤ τ/V := (div_le_div_iff_of_pos_right hV).mpr hb.le
        have hτm : τ/V ≤ τ/min U V := div_le_div_of_nonneg_left hτ.le hmin (min_le_right _ _)
        have huv : u*v ≤ v := by nlinarith
        exact huv.trans (hvτ.trans hτm)
      · have hατ : α < τ := lt_of_not_ge ha
        have huτ : u ≤ τ/U := (div_le_div_iff_of_pos_right hU).mpr hατ.le
        have hτm : τ/U ≤ τ/min U V := div_le_div_of_nonneg_left hτ.le hmin (min_le_left _ _)
        have huv : u*v ≤ u := by nlinarith
        exact huv.trans (huτ.trans hτm)
    have hp := renormalized_preliminary hα hβ hU hV hU1 hV1 hW hT hρ (hpre A B)
    change rect w A B/W ≤ C*sqrt (u*v)*((u*v)^ρ+e) at hp
    have hr := rpow_le_rpow (mul_nonneg hu hv) hsmall hρ
    calc
      rect w A B/W ≤ C*sqrt (u*v)*((u*v)^ρ+e) := hp
      _ ≤ C*sqrt (u*v)*((τ/min U V)^ρ+e) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC (sqrt_nonneg _))
      _ = sqrt (u*v)*ξ := by dsimp [ξ]; ring
      _ ≤ sqrt (u*v)*((u*v)^η+ξ) :=
        mul_le_mul_of_nonneg_left (by linarith [rpow_nonneg (mul_nonneg hu hv) η]) (sqrt_nonneg _)

end PlanarUnitDistances.IncidenceRegularization

namespace PlanarUnitDistances.GeometricExpansion
open CircleIncidence CircleCutting IncidenceRegularization
open scoped Classical
noncomputable section

def factor (m n e L dP dQ t a : ℝ) : ℝ :=
  1+1000*L^2*(m*n)^(2/3:ℝ)/e+1000*L^2*n*t^a/e+
    1000*L^2*m*t/e+dP*m/e+dQ*n/e

lemma factor_bounds {m n e L dP dQ t a : ℝ}
    (hm : 0≤ m) (hn : 0≤ n) (he : 0< e) (hdP : 0≤ dP) (hdQ : 0≤ dQ) (ht : 0< t) :
    1≤ factor m n e L dP dQ t a ∧
    1000*L^2*(m*n)^(2/3:ℝ)/e≤ factor m n e L dP dQ t a ∧
    1000*L^2*n*t^a/e≤ factor m n e L dP dQ t a ∧
    1000*L^2*m*t/e≤ factor m n e L dP dQ t a ∧
    dP*m/e≤ factor m n e L dP dQ t a ∧
    dQ*n/e≤ factor m n e L dP dQ t a := by
  have h1 : 0≤ 1000*L^2*(m*n)^(2/3:ℝ)/e := by positivity
  have h2 : 0≤ 1000*L^2*n*t^a/e := by positivity
  have h3 : 0≤ 1000*L^2*m*t/e := by positivity
  have h4 : 0≤ dP*m/e := by positivity
  have h5 : 0≤ dQ*n/e := by positivity
  unfold factor
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma incidence_degree_le (P Q : Finset Plane) {D : ℝ} (hD : ∀p∈P,degree Q p≤ D) :
    incidences P Q≤(P.card:ℝ)*D := by
  rw [incidences_comm]
  unfold incidences
  exact (Finset.sum_le_sum hD).trans_eq (by simp)

theorem preliminary_bounds (P Q : Finset Plane) {L dP dQ t a : ℝ}
    (hE : 0< incidences P Q) (hL : 1≤ L)
    (hlP : cuttingLog P.card≤ L) (hlQ : cuttingLog Q.card≤ L)
    (hdP : 0≤ dP) (hdQ : 0≤ dQ) (ht : 0< t)
    (hP : ∀p∈P,degree Q p≤ dP) (hQ : ∀q∈Q,degree P q≤ dQ) :
    ∀F⊆P,∀G⊆Q,
      let u := (F.card:ℝ)/(P.card:ℝ)
      let v := (G.card:ℝ)/(Q.card:ℝ)
      let T := factor (P.card:ℝ) (Q.card:ℝ) (incidences P Q) L dP dQ t a
      incidences F G/incidences P Q ≤ T*((u*v)^(2/3:ℝ)+t^(-a)*v+t^(-1:ℝ)*u) ∧
      incidences F G/incidences P Q ≤ T*min u v ∧
      incidences F G/incidences P Q ≤
        T*Real.sqrt (u*v)*((u*v)^(1/6:ℝ)+Real.sqrt (t^(-a))+Real.sqrt (t^(-1:ℝ))) := by
  intro F hF G hG
  dsimp only
  let m : ℝ := P.card
  let n : ℝ := Q.card
  let e := incidences P Q
  let u : ℝ := (F.card:ℝ)/m
  let v : ℝ := (G.card:ℝ)/n
  let T := factor m n e L dP dQ t a
  have hm0 : 0≤ m := Nat.cast_nonneg _
  have hn0 : 0≤ n := Nat.cast_nonneg _
  have hmn : 0< m*n := hE.trans_le (incidences_le P Q)
  have hm : 0< m := pos_of_mul_pos_left hmn hn0
  have hn : 0< n := pos_of_mul_pos_right hmn hm0
  have hu : 0≤ u := div_nonneg (Nat.cast_nonneg _) hm0
  have hv : 0≤ v := div_nonneg (Nat.cast_nonneg _) hn0
  have hT := factor_bounds hm0 hn0 hE hdP hdQ ht (a:=a) (L:=L)
  have hcF : (F.card:ℝ)=m*u := by
    dsimp only [u]
    calc
      _ = (F.card:ℝ)*(m/m) := by rw [div_self hm.ne',mul_one]
      _ = m*((F.card:ℝ)/m) := by ring
  have hcG : (G.card:ℝ)=n*v := by
    dsimp only [v]
    calc
      _ = (G.card:ℝ)*(n/n) := by rw [div_self hn.ne',mul_one]
      _ = n*((G.card:ℝ)/n) := by ring
  have hraw := incidence_bound_enlarged F G hL
    ((cuttingLog_mono (Finset.card_le_card hF)).trans hlP)
    ((cuttingLog_mono (Finset.card_le_card hG)).trans hlQ) le_rfl le_rfl
  have hmul : ((F.card:ℝ)*G.card)^(2/3:ℝ)=(m*n)^(2/3:ℝ)*(u*v)^(2/3:ℝ) := by
    rw [hcF,hcG]
    have heq : m*u*(n*v)=(m*n)*(u*v) := by ring
    rw [heq,Real.mul_rpow (mul_nonneg hm0 hn0) (mul_nonneg hu hv)]
  have htcan : t^a*t^(-a)=1 := by rw [←Real.rpow_add ht]; simp
  have htcan1 : t*t^(-1:ℝ)=1 := by rw [Real.rpow_neg_one]; exact mul_inv_cancel₀ ht.ne'
  have hlinQ : 1000*L^2*n/e ≤ T*t^(-a) := by
    have hh := mul_le_mul_of_nonneg_right hT.2.2.1 (Real.rpow_nonneg ht.le (-a))
    have heq : (1000*L^2*n*t^a/e)*t^(-a)=1000*L^2*n/e := by
      calc
        _ = (1000*L^2*n/e)*(t^a*t^(-a)) := by ring
        _ = _ := by rw [htcan,mul_one]
    change _ ≤ T*_ at hh
    rw [show (1000*L^2*n*t^a/incidences P Q)*t^(-a)=1000*L^2*n/e from heq] at hh
    exact hh
  have hlinP : 1000*L^2*m/e ≤ T*t^(-1:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hT.2.2.2.1 (Real.rpow_nonneg ht.le (-1))
    have heq : (1000*L^2*m*t/e)*t^(-1:ℝ)=1000*L^2*m/e := by
      calc
        _ = (1000*L^2*m/e)*(t*t^(-1:ℝ)) := by ring
        _ = _ := by rw [htcan1,mul_one]
    change _ ≤ T*_ at hh
    rw [show (1000*L^2*m*t/incidences P Q)*t^(-1:ℝ)=1000*L^2*m/e from heq] at hh
    exact hh
  have hinc : incidences F G/e≤ T*((u*v)^(2/3:ℝ)+t^(-a)*v+t^(-1:ℝ)*u) := by
    have hh := div_le_div_of_nonneg_right hraw hE.le
    rw [hmul,hcF,hcG] at hh
    have h0 := mul_le_mul_of_nonneg_right hT.2.1 (Real.rpow_nonneg (mul_nonneg hu hv) (2/3:ℝ))
    have h1 := mul_le_mul_of_nonneg_right hlinQ hv
    have h2 := mul_le_mul_of_nonneg_right hlinP hu
    calc
      _ ≤ 1000*L^2*((m*n)^(2/3:ℝ)*(u*v)^(2/3:ℝ)+m*u+n*v)/e := hh
      _ = (1000*L^2*(m*n)^(2/3:ℝ)/e)*(u*v)^(2/3:ℝ)+
          (1000*L^2*m/e)*u+(1000*L^2*n/e)*v := by ring
      _ ≤ _ := by nlinarith only [h0,h1,h2]
  have heP := incidence_degree_le F G (fun p hp =>
    (degree_mono hG p).trans (hP p (hF hp)))
  have heQ := incidence_degree_le G F (fun q hq =>
    (degree_mono hF q).trans (hQ q (hG hq)))
  have hp : incidences F G/e≤ T*u := by
    have hh := div_le_div_of_nonneg_right heP hE.le
    rw [hcF] at hh
    calc
      _ ≤ m*u*dP/e := hh
      _ = (dP*m/e)*u := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hT.2.2.2.2.1 hu
  have hq : incidences F G/e≤ T*v := by
    rw [incidences_comm G F] at heQ
    have hh := div_le_div_of_nonneg_right heQ hE.le
    rw [hcG] at hh
    calc
      _ ≤ n*v*dQ/e := hh
      _ = (dQ*n/e)*v := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hT.2.2.2.2.2 hv
  refine ⟨hinc,?_,?_⟩
  · change incidences F G/e ≤ T*min u v
    rcases le_total u v with h | h
    · simpa only [min_eq_left h] using hp
    · simpa only [min_eq_right h] using hq
  · exact preliminary_square_root hu hv (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg ht.le _)
      (zero_le_one.trans hT.1) hinc hp hq

theorem preliminary (P Q : Finset Plane) {L dP dQ t a : ℝ}
    (hE : 0< incidences P Q) (hL : 1≤ L)
    (hlP : cuttingLog P.card≤ L) (hlQ : cuttingLog Q.card≤ L)
    (hdP : 0≤ dP) (hdQ : 0≤ dQ) (ht : 0< t)
    (hP : ∀p∈P,degree Q p≤ dP) (hQ : ∀q∈Q,degree P q≤ dQ) :
    ∀F⊆P,∀G⊆Q,
      let u := (F.card:ℝ)/(P.card:ℝ)
      let v := (G.card:ℝ)/(Q.card:ℝ)
      let T := factor (P.card:ℝ) (Q.card:ℝ) (incidences P Q) L dP dQ t a
      incidences F G/incidences P Q ≤
        T*Real.sqrt (u*v)*((u*v)^(1/6:ℝ)+Real.sqrt (t^(-a))+Real.sqrt (t^(-1:ℝ))) := by
  intro F hF G hG
  exact (preliminary_bounds P Q hE hL hlP hlQ hdP hdQ ht hP hQ F hF G hG).2.2
end
end PlanarUnitDistances.GeometricExpansion

namespace PlanarUnitDistances.GeometricOptimizer
open CircleIncidence CircleCutting IncidenceRegularization GeometricExpansion
open scoped Classical
noncomputable section

def lift (P : Finset Plane) (A : Finset P) : Finset Plane := A.map (Function.Embedding.subtype _)
lemma lift_subset (P : Finset Plane) (A : Finset P) : lift P A⊆P := by
  intro p hp
  obtain ⟨q,_,rfl⟩ := Finset.mem_map.mp hp
  exact q.property
lemma lift_univ (P : Finset Plane) : lift P Finset.univ=P := by
  ext p
  simp [lift]
lemma lift_subtype (P A : Finset Plane) (hA : A⊆P) : lift P (A.subtype (·∈P))=A := by
  rw [lift,Finset.subtype_map]
  exact Finset.filter_eq_self.mpr (fun p hp => hA hp)
lemma subtype_subset {P A : Finset Plane} {F : Finset P} (h : A⊆lift P F) :
    A.subtype (·∈P)⊆F := by
  intro p hp
  have hh := h (Finset.mem_subtype.mp hp)
  obtain ⟨q,hq,heq⟩ := Finset.mem_map.mp hh
  have hpq : q=p := Subtype.ext heq
  simpa only [hpq] using hq

def counting (P : Finset Plane) : P → ℝ := fun _ => 1/(P.card:ℝ)
def weight (P Q : Finset Plane) : P → Q → ℝ := fun p q =>
  (if dist (p:Plane) (q:Plane)=1 then (1:ℝ) else 0)/incidences P Q
lemma counting_mass (P : Finset Plane) (A : Finset P) :
    mass (counting P) A=((lift P A).card:ℝ)/(P.card:ℝ) := by
  simp [mass,counting,lift,div_eq_mul_inv]
lemma weight_rect (P Q : Finset Plane) (A : Finset P) (B : Finset Q) :
    rect (weight P Q) A B=incidences (lift P A) (lift Q B)/incidences P Q := by
  unfold rect weight
  simp only [←Finset.sum_div]
  congr 1
  simp only [incidences,degree_sum,lift,Finset.sum_map,Function.Embedding.coe_subtype]
  exact Finset.sum_comm
lemma weight_row (P Q : Finset Plane) (p : P) (B : Finset Q) :
    (∑q∈B,weight P Q p q)=degree (lift Q B) p/incidences P Q := by
  simp only [weight,←Finset.sum_div,degree_sum,lift,Finset.sum_map,Function.Embedding.coe_subtype,dist_comm]

theorem exists_rectangle (P Q : Finset Plane) {L dP dQ t a τ : ℝ}
    (hE : 0< incidences P Q) (hL : 1≤ L)
    (hlP : cuttingLog P.card≤ L) (hlQ : cuttingLog Q.card≤ L)
    (hdP : 0≤ dP) (hdQ : 0≤ dQ) (ht : 0< t)
    (hP : ∀p∈P,degree Q p≤ dP) (hQ : ∀q∈Q,degree P q≤ dQ)
    (hτ : 0< τ) (hτ1 : τ≤ 1) :
    ∃F⊆P,∃G⊆Q,
      let U := (F.card:ℝ)/(P.card:ℝ)
      let V := (G.card:ℝ)/(Q.card:ℝ)
      let W := incidences F G/incidences P Q
      let T := factor (P.card:ℝ) (Q.card:ℝ) (incidences P Q) L dP dQ t a
      let e := Real.sqrt (t^(-a))+Real.sqrt (t^(-1:ℝ))
      let ξ := (T*Real.sqrt (U*V)/W)*((τ/min U V)^(1/6:ℝ)+e)
      τ≤ U ∧ τ≤ V ∧ 0< W ∧ (U*V)^(27/50:ℝ)≤ W ∧
      (∀A⊆F,∀B⊆G,incidences A B/incidences F G≤
        Real.sqrt ((A.card:ℝ)/F.card*((B.card:ℝ)/G.card))*
          (((A.card:ℝ)/F.card*((B.card:ℝ)/G.card))^(1/25:ℝ)+ξ)) ∧
      (τ≤ U-1/(P.card:ℝ) → ∀p∈F,(27/50:ℝ)/(F.card:ℝ)≤ degree G p/incidences F G) ∧
      (τ≤ V-1/(Q.card:ℝ) → ∀q∈G,(27/50:ℝ)/(G.card:ℝ)≤ degree F q/incidences F G) := by
  have hmn : 0<(P.card:ℝ)*(Q.card:ℝ) := hE.trans_le (incidences_le P Q)
  have hm : 0<(P.card:ℝ) := pos_of_mul_pos_left hmn (Nat.cast_nonneg _)
  have hn : 0<(Q.card:ℝ) := pos_of_mul_pos_right hmn (Nat.cast_nonneg _)
  have hμ : ∀p,0≤ counting P p := fun _ => div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hν : ∀q,0≤ counting Q q := fun _ => div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hμs : ∑p,counting P p=1 := by
    change mass (counting P) Finset.univ=1
    rw [counting_mass,lift_univ,div_self hm.ne']
  have hνs : ∑q,counting Q q=1 := by
    change mass (counting Q) Finset.univ=1
    rw [counting_mass,lift_univ,div_self hn.ne']
  have hws : ∑p,∑q,weight P Q p q=1 := by
    change rect (weight P Q) Finset.univ Finset.univ=1
    rw [weight_rect,lift_univ,lift_univ,div_self hE.ne']
  obtain ⟨F,G,hmax,hwin⟩ := exists_maximizing (counting P) (counting Q) (weight P Q)
    (γ:=(1/2:ℝ)+1/25) hτ1 hμs hνs hws
  obtain ⟨hU,hV,hW,hpow⟩ := winner_positive (counting P) (counting Q) (weight P Q) hτ hmax hwin
  let T := factor (P.card:ℝ) (Q.card:ℝ) (incidences P Q) L dP dQ t a
  let err := Real.sqrt (t^(-a))+Real.sqrt (t^(-1:ℝ))
  have hT0 : 0≤ T := zero_le_one.trans (factor_bounds (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hE hdP hdQ ht (a:=a) (L:=L)).1
  have hpre (A : Finset P) (B : Finset Q) : rect (weight P Q) A B≤
      T*Real.sqrt (mass (counting P) A*mass (counting Q) B)*
        ((mass (counting P) A*mass (counting Q) B)^(1/6:ℝ)+err) := by
    rw [weight_rect,counting_mass,counting_mass]
    simpa only [T,err,add_assoc] using preliminary (a:=a) P Q hE hL hlP hlQ hdP hdQ ht hP hQ (lift P A) (lift_subset P A)
      (lift Q B) (lift_subset Q B)
  have hexp := maximizing_expansion (counting P) (counting Q) (weight P Q)
    hμ hν hμs hνs hτ (by norm_num : (0:ℝ)≤ 1/25) (by norm_num : (0:ℝ)≤ 1/6)
    hT0 (show 0≤ err by dsimp [err]; positivity) hmax hW hpre
  let FP := lift P F
  let GQ := lift Q G
  have hFP : 0<(FP.card:ℝ) := by
    have hh := hU
    rw [counting_mass] at hh
    exact (div_pos_iff_of_pos_right hm).mp hh
  have hGQ : 0<(GQ.card:ℝ) := by
    have hh := hV
    rw [counting_mass] at hh
    exact (div_pos_iff_of_pos_right hn).mp hh
  have hFG : 0< incidences FP GQ := by
    rw [weight_rect] at hW
    exact (div_pos_iff_of_pos_right hE).mp hW
  refine ⟨FP,lift_subset P F,GQ,lift_subset Q G,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [counting_mass] using hmax.1
  · simpa only [counting_mass] using hmax.2.1
  · simpa only [weight_rect] using hW
  · norm_num only at hpow
    simpa only [counting_mass,weight_rect] using hpow
  · intro A hA B hB
    let As := A.subtype (·∈P)
    let Bs := B.subtype (·∈Q)
    have hAP : A⊆P := hA.trans (lift_subset P F)
    have hBQ : B⊆Q := hB.trans (lift_subset Q G)
    have hAs : lift P As=A := lift_subtype P A hAP
    have hBs : lift Q Bs=B := lift_subtype Q B hBQ
    have hh := hexp As (subtype_subset hA) Bs (subtype_subset hB)
    simp only [counting_mass,weight_rect,hAs,hBs] at hh
    have hnormA : ((A.card:ℝ)/P.card)/((FP.card:ℝ)/P.card)=(A.card:ℝ)/FP.card := by field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne',hE.ne',hFG.ne']
    have hnormB : ((B.card:ℝ)/Q.card)/((GQ.card:ℝ)/Q.card)=(B.card:ℝ)/GQ.card := by field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne',hE.ne',hFG.ne']
    have hnormE : (incidences A B/incidences P Q)/(incidences FP GQ/incidences P Q)=
        incidences A B/incidences FP GQ := by field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne',hE.ne',hFG.ne']
    dsimp only [FP,GQ] at hnormA hnormB hnormE
    simpa only [hnormA,hnormB,hnormE,FP,GQ,T,err] using hh
  · intro he p hp
    obtain ⟨ps,hps,hpseq⟩ := Finset.mem_map.mp hp
    have her : τ≤ mass (counting P) (F.erase ps) := by
      have hh : mass (counting P) (F.erase ps)+counting P ps=mass (counting P) F :=
        Finset.sum_erase_add _ _ hps
      simp only [counting_mass,counting] at hh ⊢
      dsimp only [FP,GQ] at he
      linarith
    have hh := left_atom_bound (counting P) (counting Q) (weight P Q) hμ hτ
      (by norm_num : (0:ℝ)≤ 1/2+1/25) (by norm_num : (1/2:ℝ)+1/25≤ 1) hmax hW hps her
    rw [counting_mass,weight_row,weight_rect] at hh
    norm_num only at hh
    have hca : counting P ps/((FP.card:ℝ)/P.card)=1/(FP.card:ℝ) := by dsimp [counting]; field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne']
    have hce : (degree GQ ps/incidences P Q)/(incidences FP GQ/incidences P Q)=degree GQ ps/incidences FP GQ := by field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne',hE.ne',hFG.ne']
    rw [hca,hce] at hh
    change (ps:Plane)=p at hpseq
    simpa only [hpseq,mul_one_div] using hh
  · intro he q hq
    obtain ⟨qs,hqs,hqseq⟩ := Finset.mem_map.mp hq
    have her : τ≤ mass (counting Q) (G.erase qs) := by
      have hh : mass (counting Q) (G.erase qs)+counting Q qs=mass (counting Q) G :=
        Finset.sum_erase_add _ _ hqs
      simp only [counting_mass,counting] at hh ⊢
      dsimp only [FP,GQ] at he
      linarith
    have hh := right_atom_bound (counting P) (counting Q) (weight P Q) hν hτ
      (by norm_num : (0:ℝ)≤ 1/2+1/25) (by norm_num : (1/2:ℝ)+1/25≤ 1) hmax hW hqs her
    have hcol : (∑p∈F,weight P Q p qs)=degree FP qs/incidences P Q := by
      simp only [weight,←Finset.sum_div,degree_sum,FP,lift,Finset.sum_map,Function.Embedding.coe_subtype]
      congr 1

    rw [counting_mass,hcol,weight_rect] at hh
    norm_num only at hh
    have hca : counting Q qs/((GQ.card:ℝ)/Q.card)=1/(GQ.card:ℝ) := by dsimp [counting]; field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne']
    have hce : (degree FP qs/incidences P Q)/(incidences FP GQ/incidences P Q)=degree FP qs/incidences FP GQ := by field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne',hE.ne',hFG.ne']
    rw [hca,hce] at hh
    change (qs:Plane)=q at hqseq
    simpa only [hqseq,mul_one_div] using hh
end
end PlanarUnitDistances.GeometricOptimizer
end OAI
