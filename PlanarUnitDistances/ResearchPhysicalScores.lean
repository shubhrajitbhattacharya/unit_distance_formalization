import PlanarUnitDistances.ResearchPhysicalModel
import PlanarUnitDistances.LogHeight

namespace PlanarUnitDistances.ResearchPhysical
open OAI.PlanarUnitDistances CommonFieldModel Competition Finset
open scoped Classical
noncomputable section
variable {P Q : Finset Competition.Plane}

/-- Original order ((p,r),q) and explicit-edge order (p,q,r). -/
def reorder (M : Model P Q) : ((P × P) × Q) ≃ Triple (toPiece M) where
  toFun x := (x.1.1,x.2,x.1.2)
  invFun x := ((x.1,x.2.2),x.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

theorem reorder_sum (M : Model P Q) (F : Triple (toPiece M) → ℝ) :
    (∑ x, F (reorder M x)) = ∑ y, F y := (reorder M).sum_comp F

def endpoint (M : Model P Q) (d : Scores (toPiece M)) (p : P) : HeightPlace M.field → ℝ :=
  Sum.elim (d.arch p) (d.finite p)

theorem endpoint_finite (M : Model P Q) (d : Scores (toPiece M)) (p : P) :
    FiniteAtPrimes (endpoint M d p) := by
  change (Function.support (d.finite p)).Finite
  rw [Finsupp.fun_support_eq]
  exact (d.finite p).support.finite_toSet

theorem endpoint_width_nonnegative (M : Model P Q) (d : Scores (toPiece M))
    (b : MomentBounds (toPiece M) d) (hQ : Q.Nonempty) (p : P) : 0≤d.H p := by
  obtain ⟨q,hq⟩ := hQ
  have h := b.width_nn (p,⟨q,hq⟩,p)
  change 0≤d.H p+d.H p at h
  linarith

theorem signed_eq (M : Model P Q) (d : Scores (toPiece M)) (p r : P) (q : Q) :
    signedError d (p,q,r) =
      placeNorm (localLog ((M.z (.inl p)-M.z (.inr q))/(M.z (.inl r)-M.z (.inr q))) -
        (endpoint M d r-endpoint M d p)) := by
  unfold signedError placeNorm
  rw [ratio]
  rfl

theorem unsigned_lower (M : Model P Q) (d : Scores (toPiece M))
    (b : MomentBounds (toPiece M) d) (p r : P) (q : Q)
    (hm : 0<(toPiece M).mass (p,q,r))
    (hne : (M.z (.inl p)-M.z (.inr q))/(M.z (.inl r)-M.z (.inr q))≠0) :
    d.H p+d.H r-d.error (p,q,r) ≤
      placeNorm (localLog ((M.z (.inl p)-M.z (.inr q))/(M.z (.inl r)-M.z (.inr q)))) := by
  have h := (abs_le.mp (b.unsigned (p,q,r) hm)).1
  rw [ratio] at h
  have m := twice_weilHeight_eq_absLog hne
  change 2*weilHeight _ = placeNorm (localLog _) at m
  rw [←m]
  change -d.error (p,q,r) ≤ 2*weilHeight _-(d.H p+d.H r) at h
  linarith

end
end PlanarUnitDistances.ResearchPhysical

