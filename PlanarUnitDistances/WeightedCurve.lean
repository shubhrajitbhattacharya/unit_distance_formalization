import PlanarUnitDistances.CurveRestriction
import PlanarUnitDistances.CurveProduct

/-! Factor induction adapted from OpenAI, UnitDistances/Derivations.lean,
`irreducible_zero_capture`, Apache-2.0, tree ab85655b8737cadc023a25809bdf1b8372563c23.
We use the actual total degree and sum the original degrees of the vertices. -/
namespace PlanarUnitDistances.CurveRestriction
open MvPolynomial Finset
open scoped Classical
noncomputable section
variable {k P Q : Type*} [Field k]
abbrev Poly (k : Type*) [Field k] := MvPolynomial (Fin 2) k

def zeroWeight (S : Finset P) (x : P → Fin 2 → k) (w : P → ℕ) (f : Poly k) : ℕ :=
  ∑ p ∈ S, if eval (x p) f = 0 then w p else 0

private lemma degree_pos {f : Poly k} (h : f ≠ 0) (nu : ¬IsUnit f) : 0 < f.totalDegree := by
  by_contra! he
  have hf := (totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp he))
  have hn : f.coeff 0 ≠ 0 := fun hc => h (by simpa [hc] using hf)
  exact nu (hf ▸ (isUnit_iff_ne_zero.mpr hn).map C)

theorem irreducible_weight_capture (S : Finset P) (x : P → Fin 2 → k) (w : P → ℕ)
    (f : Poly k) (hf : f ≠ 0) (nu : ¬IsUnit f) :
    ∃ g : Poly k, Irreducible g ∧ g ∣ f ∧ g.totalDegree ≤ f.totalDegree ∧
      zeroWeight S x w f ≤ f.totalDegree*zeroWeight S x w g := by
  generalize hd : f.totalDegree=d
  induction d using Nat.strong_induction_on generalizing f with
  | h d ih =>
    by_cases ir : Irreducible f
    · exact ⟨f,ir,dvd_refl _,hd.le,Nat.le_mul_of_pos_left _ (hd ▸ degree_pos hf nu)⟩
    obtain ⟨g,h,ef,ng,nh⟩ : ∃ g h, f=g*h ∧ ¬IsUnit g ∧ ¬IsUnit h := by
      simpa [irreducible_iff,nu] using ir
    have hg := left_ne_zero_of_mul (ef ▸ hf)
    have hh := right_ne_zero_of_mul (ef ▸ hf)
    have sumD : g.totalDegree+h.totalDegree=d := by rw [←totalDegree_mul_of_isDomain hg hh,←ef,hd]
    have gp := degree_pos hg ng
    have hp := degree_pos hh nh
    obtain ⟨u,iu,du,su,wu⟩ := ih g.totalDegree (by omega) g hg ng rfl
    obtain ⟨v,iv,dv,sv,wv⟩ := ih h.totalDegree (by omega) h hh nh rfl
    have total : zeroWeight S x w f ≤ zeroWeight S x w g+zeroWeight S x w h := by
      unfold zeroWeight
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro p _
      rw [ef,map_mul]
      by_cases h₁ : eval (x p) g=0 <;> by_cases h₂ : eval (x p) h=0 <;> simp [h₁,h₂]
    rcases le_total (zeroWeight S x w u) (zeroWeight S x w v) with hl|hl
    · refine ⟨v,iv,dv.trans (ef ▸ dvd_mul_left h g),by omega,?_⟩
      rw [←sumD,add_mul]
      exact total.trans (Nat.add_le_add (wu.trans (Nat.mul_le_mul_left _ hl)) wv)
    · refine ⟨u,iu,du.trans (ef ▸ dvd_mul_right g h),by omega,?_⟩
      rw [←sumD,add_mul]
      exact total.trans (Nat.add_le_add wu (wv.trans (Nat.mul_le_mul_left _ hl)))

/-- From one actual low-degree equation on each quadruple's neighbors to
an irreducible curve retaining the asserted number of original edges. -/
theorem irreducible_curve_restriction [Fintype P] [Fintype Q] {n D : ℕ} (hn : 0<n) (hD : 0<D)
    (hp : Fintype.card P ≤ n) (hq : Fintype.card Q ≤ n) (x : P → Fin 2 → k)
    (N : P → Finset Q) (dense : 16*n ≤ ∑ p, (N p).card)
    (anchors : ∀ a : Fin 4 ↪ Q, ∃ f : Poly k, f ≠ 0 ∧ f.totalDegree ≤ D ∧
      ∀ p ∈ common N a, eval (x p) f=0) :
    ∃ g : Poly k, Irreducible g ∧ g.totalDegree ≤ D ∧
      ((∑ p, (N p).card : ℕ):ℝ)^5/(512*D*(n:ℝ)^8) ≤
        ∑ p ∈ univ.filter (fun p => eval (x p) g=0), ((N p).card:ℝ) := by
  haveI : Nonempty P := by
    by_contra! h
    letI : IsEmpty P := h
    simp at dense
    omega
  obtain ⟨a,hm⟩ := four_anchors hn hp hq N dense
  obtain ⟨f,hf,df,allz⟩ := anchors a
  let S := common N a
  let w (p : P) := (N p).card
  have epos : 0 < ∑ p, (N p).card := by omega
  have lhs : 0 < (((∑ p, (N p).card:ℕ):ℝ)^5)/(512*(n:ℝ)^8) := by positivity
  have sn : S.Nonempty := by
    by_contra! he
    change _ ≤ ∑ p ∈ S, ((N p).card:ℝ) at hm
    rw [he,Finset.sum_empty] at hm
    exact (not_lt_of_ge hm) lhs
  have nu : ¬IsUnit f := by
    obtain ⟨p,hs⟩ := sn
    intro hu
    exact (hu.map (eval (x p))).ne_zero (allz p hs)
  obtain ⟨g,ig,_,dg,wg⟩ := irreducible_weight_capture S x w f hf nu
  refine ⟨g,ig,dg.trans df,?_⟩
  have wz : zeroWeight S x w f=∑ p ∈ S,w p := by
    unfold zeroWeight
    exact Finset.sum_congr rfl fun p h => if_pos (allz p h)
  have wc : zeroWeight S x w g ≤ ∑ p ∈ univ.filter (fun p => eval (x p) g=0),w p := by
    rw [zeroWeight,Finset.sum_filter]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [wz] at wg
  have hnat := wg.trans (Nat.mul_le_mul df wc)
  have hreal : (∑ p ∈ S, ((N p).card:ℝ)) ≤
      (D:ℝ)*∑ p ∈ univ.filter (fun p => eval (x p) g=0), ((N p).card:ℝ) := by exact_mod_cast hnat
  have hfinal := hm.trans hreal
  apply (div_le_iff₀ (by positivity)).mpr
  have hfin := (div_le_iff₀ (by positivity)).mp hfinal
  linarith only [hfin]

end
end PlanarUnitDistances.CurveRestriction
