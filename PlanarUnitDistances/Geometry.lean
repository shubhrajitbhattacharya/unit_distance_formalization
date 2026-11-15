import PlanarUnitDistances.Specialization

namespace PlanarUnitDistances
open OAI.PlanarUnitDistances
open scoped ComplexConjugate

def zCoord (p : Plane) : ℂ := ⟨p 0, p 1⟩

theorem zCoord_sub_normSq (p q : Plane) :
    Complex.normSq (zCoord p - zCoord q) = dist p q ^ 2 := by
  rw [PrimitiveChart.plane_dist_sq, Complex.normSq_apply]
  simp [zCoord, pow_two]

theorem unit_edge_reciprocal {p q : Plane} (h : dist p q = 1) :
    (zCoord p - zCoord q) * (conj (zCoord p) - conj (zCoord q)) = 1 := by
  rw [← map_sub, Complex.mul_conj, zCoord_sub_normSq, h]
  norm_num

/-- A signed, algebraic identity using the same orientation on both edges. -/
theorem chord_identity {K : Type*} [Field K] {d e D E : K}
    (hp : d * D = 1) (hr : e * E = 1) :
    (d-e)*(D-E) = 2 - d/e - (d/e)⁻¹ ∧
    ((d/e)⁻¹ - d/e)^2 = ((d-e)*(D-E)) * (((d-e)*(D-E)) - 4) := by
  have hd : d ≠ 0 := by rintro rfl; simp at hp
  have he : e ≠ 0 := by rintro rfl; simp at hr
  have hD : D = d⁻¹ := by apply mul_left_cancel₀ hd; simpa [hd] using hp
  have hE : E = e⁻¹ := by apply mul_left_cancel₀ he; simpa [he] using hr
  subst D; subst E
  constructor <;> rw [inv_div] <;> field_simp <;> ring

theorem planar_chord_identities {p r q : Plane} (hp : dist p q = 1) (hr : dist r q = 1) :
    let lam := (zCoord p - zCoord q) / (zCoord r - zCoord q)
    let L : ℂ := (dist p r ^ 2 : ℝ)
    L = 2 - lam - lam⁻¹ ∧ (lam⁻¹ - lam)^2 = L * (L - 4) := by
  have h := chord_identity (unit_edge_reciprocal hp) (unit_edge_reciprocal hr)
  simp only [sub_sub_sub_cancel_right, ← map_sub, Complex.mul_conj, zCoord_sub_normSq] at h
  exact h

/-- The degree-two obstruction in the three-center test, valid before any embedding.
The two point coordinates in the second slot may be equal. -/
theorem common_centers_le_two {K ι : Type*} [Field K]
    (s : Finset ι) (z w : ι → K) (hinj : Set.InjOn z (s : Set ι))
    {zp zr wp wr : K} (hpr : zr ≠ zp)
    (hp : ∀ q ∈ s, (zp - z q) * (wp - w q) = 1)
    (hr : ∀ q ∈ s, (zr - z q) * (wr - w q) = 1) :
    s.card ≤ 2 := by
  classical
  let u := zr-zp
  let v := wr-wp
  let d := fun q => zp-z q
  have hu : u ≠ 0 := sub_ne_zero.mpr hpr
  have root (q : ι) (hq : q ∈ s) : v * (d q)^2 + u*v*d q + u = 0 := by
    dsimp [u,v,d]
    linear_combination (zp-z q)*(hr q hq) - (zr-z q)*(hp q hq)
  have hdinj : Set.InjOn d (s : Set ι) := fun _ ha _ hb hab =>
    hinj ha hb (sub_right_inj.mp hab)
  let f : Polynomial K := Polynomial.C v * Polynomial.X^2 +
    Polynomial.C (u*v) * Polynomial.X + Polynomial.C u
  have hf : f ≠ 0 := by
    intro h
    have he := congrArg (Polynomial.eval 0) h
    simp [f, hu] at he
  have hdeg : f.natDegree ≤ 2 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le _ (by simp)
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact Polynomial.natDegree_mul_le.trans (by simp only [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]; decide)
    · exact Polynomial.natDegree_mul_le.trans (by simp only [Polynomial.natDegree_C, Polynomial.natDegree_X]; decide)
  rw [← Finset.card_image_of_injOn hdinj]
  apply le_trans (b := f.natDegree) _ hdeg
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
  apply (Polynomial.mem_roots hf).mpr
  simpa [f] using root q hq

end PlanarUnitDistances
