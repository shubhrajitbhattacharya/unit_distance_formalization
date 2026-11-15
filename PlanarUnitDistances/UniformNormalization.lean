import PlanarUnitDistances.EdgeHeightScale
import PlanarUnitDistances.GraphHeightTransfer
import PlanarUnitDistances.UniformGraphHeight

namespace PlanarUnitDistances.UniformNormalization
open Finset BoundedHeight EdgeHeightScale OAI.PlanarUnitDistances.LocalHeightTransfer
open scoped Classical
noncomputable section
variable {P Q : Type} [Fintype P] [Fintype Q]
variable {K : Type*} [Field K] [NumberField K]

def weight (S : Q → Finset P) (e : ℝ) (p : P) (q : Q) := if p ∈ S q then e⁻¹ else 0

def direction (S : Q → Finset P) (Z : P ⊕ Q → K) (x : P × Q) :=
  if x.1 ∈ S x.2 then Z (.inl x.1)-Z (.inr x.2) else 1

def profileScale (S : Q → Finset P) (e : ℝ) (Z : P ⊕ Q → K) (l u : AbsoluteValue K ℝ → ℝ) :=
  placeSum (minorityIntegral (fun x : P × Q => weight S e x.1 x.2) (direction S Z) l u)

omit [Fintype P] in
theorem weight_left (S : Q → Finset P) (e : ℝ) (p : P) :
    left (weight S e) p = ((pointCenters S p).card : ℝ)/e := by
  simp [left,weight,pointCenters,div_eq_mul_inv,← Finset.sum_filter]

omit [Fintype Q] in
theorem weight_right (S : Q → Finset P) (e : ℝ) (q : Q) :
    ∑ p, weight S e p q = centerLaw S e q := by
  simp [weight,centerLaw,div_eq_mul_inv]

/-- Normalize the actual unit directions in a uniformly weighted graph, using its
own threshold integral and one of its own positive-mass edges. -/
theorem normalize (S : Q → Finset P) {e : ℝ} (he : 0 < e)
    (ht : ∑ q, ((S q).card : ℝ) = e) (hc : LabelControl 28 (weight S e))
    (Z W : P ⊕ Q → K) (hinjP : Function.Injective (Z ∘ Sum.inl))
    (hinjQ : Function.Injective (Z ∘ Sum.inr))
    (hedge : ∀ q p, p ∈ S q → (Z (.inl p)-Z (.inr q))*(W (.inl p)-W (.inr q))=1)
    (l u : AbsoluteValue K ℝ → ℝ) (hl : ∀ v x, l v ≤ threshold v (direction S Z) x)
    (hu : ∀ v x, threshold v (direction S Z) x ≤ u v) :
    ∃ (z w : P ⊕ Q → K), Function.Injective (z ∘ Sum.inl) ∧ Function.Injective (z ∘ Sum.inr) ∧
      (∀ q p, p ∈ S q → (z (.inl p)-z (.inr q))*(w (.inl p)-w (.inr q))=1) ∧
      (∑ p, ((pointCenters S p).card : ℝ)/e * (weilHeight (z (.inl p))+weilHeight (w (.inl p)))) +
      (∑ q, centerLaw S e q * (weilHeight (z (.inr q))+weilHeight (w (.inr q)))) ≤
        226*(profileScale S e Z l u + 1) := by
  classical
  let m (x : P × Q) := weight S e x.1 x.2
  let d := direction S Z
  have hw (p : P) (q : Q) : 0 ≤ weight S e p q := by dsimp [weight]; split <;> positivity
  have sm : ∑ p, ∑ q, weight S e p q = 1 := by
    rw [sum_comm]
    simp only [weight_right,centerLaw,← sum_div,ht,div_self he.ne']
  have hm : ∑ x, m x = 1 := by rw [Fintype.sum_prod_type]; exact sm
  have hd (x : P × Q) : d x ≠ 0 := by
    dsimp [d,direction]
    split_ifs with h
    · exact left_ne_zero_of_mul_eq_one (hedge _ _ h)
    · exact one_ne_zero
  obtain ⟨f,_,hf⟩ := exists_reference_edge m (fun x => hw _ _) hm d hd l u hl hu
  have hz : (∑ p, ∑ q, weight S e p q * weilHeight ((Z (.inl p)-Z (.inr q))/d f)) ≤
      profileScale S e Z l u := by
    refine le_trans (le_of_eq ?_) hf
    rw [Fintype.sum_prod_type]
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro q _
    by_cases h : p ∈ S q <;> simp [d,m,weight,direction,h]
  have unit (p : P) (q : Q) (hp : weight S e p q ≠ 0) :
      (Z (.inl p)-Z (.inr q))*(W (.inl p)-W (.inr q))=1 := by
    apply hedge
    by_contra h
    exact hp (by simp [weight,h])
  obtain ⟨o,ho,havg⟩ := HeightTransfer.edge_scale_normalization hw sm hc Z W unit (hd f) hz
  let z := fun i => (Z i - Z (.inl o))/d f
  let w := fun i => d f * (W i - W (.inl o))
  have cancel (i j : P ⊕ Q) (h : z i=z j) : Z i=Z j :=
    sub_left_inj.mp ((div_left_inj' (hd f)).mp h)
  refine ⟨z,w,fun a b h => hinjP (cancel _ _ h),fun a b h => hinjQ (cancel _ _ h),?_,?_⟩
  · intro q p hp
    exact ho p q (by simp [weight,hp,he.ne'])
  · simpa only [z,w,weight_left,weight_right] using havg

end
end PlanarUnitDistances.UniformNormalization
