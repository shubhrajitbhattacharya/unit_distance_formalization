import PlanarUnitDistances.PhysicalInterface
import PlanarUnitDistances.EuclideanIdentity
import PlanarUnitDistances.LogHeight

/-! The edge selected by the actual triple law, with its original field and embedding. -/
namespace PlanarUnitDistances.Competition
open Finset
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

private theorem squared_distance (p r : Plane) :
    (z p-z r)*(star (z p)-star (z r)) = ((dist p r ^ 2 : ℝ):ℂ) := by
  rw [←star_sub]
  change (z p-z r)*starRingEnd ℂ (z p-z r) = _
  rw [Complex.mul_conj]
  congr 1
  rw [Complex.normSq_apply,EuclideanSpace.dist_sq_eq,Fin.sum_univ_two]
  simp only [z,Complex.sub_re,Complex.sub_im,Real.dist_eq,sq_abs]
  ring

theorem unit_model (M : IncidencePiece K) {p q : Plane} (h : (p,q)∈M.E) :
    (M.Z p-M.Z q)*(M.W p-M.W q)=1 := by
  obtain ⟨hp,hq⟩ := mem_product.mp (M.membership h)
  obtain ⟨zp,wp⟩ := M.coordinates p (mem_union_left _ hp)
  obtain ⟨zq,wq⟩ := M.coordinates q (mem_union_right _ hq)
  apply M.embedding.injective
  rw [map_mul,map_sub,map_sub,map_one,zp,wp,zq,wq,squared_distance,M.unit _ h]
  norm_num

/-- On each triple of positive mass the physical ratio is a nonzero element of K,
and the squared Euclidean chord of the actual real endpoints is its trace expression. -/
theorem supported_chord (M : IncidencePiece K) (x : Triple M) (hm : 0 < M.mass x) :
    tripleRatio M x ≠ 0 ∧ ((dist x.1.val x.2.2.val ^ 2 : ℝ):ℂ) =
      2-M.embedding (tripleRatio M x)-(M.embedding (tripleRatio M x))⁻¹ := by
  rcases x with ⟨p,q,r⟩
  have supp : (p.val,q.val)∈M.E ∧ (r.val,q.val)∈M.E := by
    by_contra hh
    simp [IncidencePiece.mass,hh] at hm
  have ep := unit_model M supp.1
  have er := unit_model M supp.2
  have n1 : M.Z p-M.Z q ≠ 0 := fun h => by simp [h] at ep
  have n2 : M.Z r-M.Z q ≠ 0 := fun h => by simp [h] at er
  refine ⟨div_ne_zero n1 n2,?_⟩
  have h := congrArg M.embedding (EuclideanIdentity.chord ep er).1
  rw [sub_sub_sub_cancel_right,sub_sub_sub_cancel_right] at h
  obtain ⟨zp,wp⟩ := M.coordinates p (mem_union_left _ p.prop)
  obtain ⟨zr,wr⟩ := M.coordinates r (mem_union_left _ r.prop)
  simp only [map_mul,map_sub,map_ofNat,map_inv₀,zp,wp,zr,wr,squared_distance] at h
  exact h


end
end PlanarUnitDistances.Competition
