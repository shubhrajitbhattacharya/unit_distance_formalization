import PlanarUnitDistances.ArithmeticTailMeans
import PlanarUnitDistances.GeometricWidthTail
import PlanarUnitDistances.PhysicalScores

namespace PlanarUnitDistances.Competition.IncidencePiece
open Finset Real NumberField
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]


theorem arithmetic_width_tail (M : IncidencePiece K) {t : ℝ} (reg : Regular M t) (ht : 0<t)
    (hS : (2:ℝ)^2100<M.scale) (hξ : t^(-150*savingG)≤1/(2:ℝ)^72) (hdeg : ∀p∈M.P,2≤M.degreeP p)
    (F : Finset (FinitePlace K)) (l h : AbsoluteValue K ℝ→ℝ) (u : InfinitePlace K→ℝ)
    (d : CoordinateLevel M.Label→M.Label)
    (hv : ∀r,M.goodRare r → M.pointMass (fun p => r.selected p≠d r)+M.centerMass (fun q => r.selected q≠d r)
       ≤2*(M.minorityMass r+M.inconsistentMass r))
    (hmin : M.placeIntegral F l h u M.minorityMass=M.scale)
    (hbad : M.placeIntegral F l h u M.inconsistentMass≤2*sqrt 2)
    (hpair : ∀p∈M.P,∀q r : Plane,(p,q)∈M.E → (p,r)∈M.E → q≠r →
      2*M.vertexWidth F l h u d p ≤ 3*(M.vertexWidth F l h u d q+M.inconsistentLength F l h u (p,q)+
        (M.vertexWidth F l h u d r+M.inconsistentLength F l h u (p,r)))+2*M.scale/eps) :
    let s := M.arithmeticScores F l h u d
    (∑v : Triple M,M.mass v*(if 8*M.scale/eps<s.width v then s.width v else 0))≤(2:ℝ)^14/2^144*M.scale := by
  let X := M.vertexWidth F l h u d
  let m := M.inconsistentLength F l h u
  obtain ⟨X0,m0,hX,hY,hm⟩ := M.arithmetic_tail_means hS F l h u d hv hmin hbad
  apply (M.geometric_width_tail reg ht ((by positivity : 0<(2:ℝ)^2100).trans hS) _ hξ hdeg X X m
    (fun e _ => X0 e.1) (fun e _ => X0 e.2) (fun e _ => m0 e) hX hY hm hpair).2
  apply (le_div_iff₀ (by positivity)).mpr
  apply le_trans _ hS.le
  calc
    (192:ℝ)*2^144 ≤ 2^8*2^144 := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = (2:ℝ)^(8+144) := (pow_add ..).symm
    _ ≤ (2:ℝ)^2100 := pow_le_pow_right₀ (by norm_num) (by decide : (8+144:ℕ)≤2100)

end
end PlanarUnitDistances.Competition.IncidencePiece

