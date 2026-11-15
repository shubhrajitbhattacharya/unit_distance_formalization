import PlanarUnitDistances.UniformNormalization
import PlanarUnitDistances.BoundedHeightTheorem

namespace PlanarUnitDistances.UniformNormalization
open BoundedHeight EdgeHeightScale OAI.PlanarUnitDistances.LocalHeightTransfer Finset
noncomputable section
/-- The small-height branch is excluded at the manuscript's exact exponent, for
the original directions of the same edge law. In particular the normalization
cannot change the scale appearing in the conclusion. -/
theorem scale_large {P Q : Type} [Fintype P] [Fintype Q] {K : Type*} [Field K] [NumberField K]
    (S : Q → Finset P) (hrow : ∀ q, (S q).Nonempty) {e : ℝ} (he : 0 < e)
    (hm : ∑ q, ((S q).card : ℝ) = e) (hc : LabelControl 28 (weight S e))
    (Z W : P ⊕ Q → K) (hinjP : Function.Injective (Z ∘ Sum.inl))
    (hinjQ : Function.Injective (Z ∘ Sum.inr))
    (hedge : ∀ q p, p ∈ S q → (Z (.inl p)-Z (.inr q))*(W (.inl p)-W (.inr q))=1)
    (l u : AbsoluteValue K ℝ → ℝ) (hl : ∀ v x, l v ≤ threshold v (direction S Z) x)
    (hu : ∀ v x, threshold v (direction S Z) x ≤ u v)
    {θ t : ℝ} (hθ : 0 ≤ θ) (ht : 0 < t) (htθ : t*θ ≤ 1/100)
    (hatom : ∀ p, ((pointCenters S p).card : ℝ)/e ≤ θ)
    (hdeg : ∀ p, (300:ℝ) ≤ (pointCenters S p).card)
    (hD : twoEdgeInformation S e + 1 ≤ 30600*exactGap*Real.log t) :
    (2:ℝ)^2100 < profileScale S e Z l u := by
  obtain ⟨z,w,hp,hq,unit,hh⟩ := normalize S he hm hc Z W hinjP hinjQ hedge l u hl hu
  have h := small_height_endpoint S hrow he hm (z ∘ Sum.inl) (w ∘ Sum.inl)
    (z ∘ Sum.inr) (w ∘ Sum.inr) hp hq unit hθ ht htθ hatom hdeg hD
  have htotal := lt_of_lt_of_le h hh
  change 226*((2:ℝ)^2100+1) < 226*(profileScale S e Z l u + 1) at htotal
  exact (add_lt_add_iff_right 1).mp ((mul_lt_mul_iff_right₀ (by norm_num : (0:ℝ)<226)).mp htotal)

end
end PlanarUnitDistances.UniformNormalization
