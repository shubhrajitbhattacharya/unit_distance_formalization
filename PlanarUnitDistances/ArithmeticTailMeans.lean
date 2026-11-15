import PlanarUnitDistances.TailUniformEdge
import PlanarUnitDistances.LocalEndpoint

namespace PlanarUnitDistances.Competition.IncidencePiece
open Finset Real NumberField
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

/-- The same good-rare exceptional width applies to a vertex on either side. -/
def vertexWidth (M : IncidencePiece K) (F : Finset (FinitePlace K)) (l h : AbsoluteValue K ℝ→ℝ)
    (u : InfinitePlace K→ℝ) (d : CoordinateLevel M.Label→M.Label) (p : Plane) :=
  M.placeIntegral F l h u (M.endpointWidth d p)

def inconsistentLength (M : IncidencePiece K) (F : Finset (FinitePlace K)) (l h : AbsoluteValue K ℝ→ℝ)
    (u : InfinitePlace K→ℝ) (e : Plane×Plane) :=
  M.placeIntegral F l h u (fun r => if ¬r.consistent e then (1:ℝ) else 0)

theorem edgeMean_placeIntegral (M : IncidencePiece K) (F : Finset (FinitePlace K)) (l h : AbsoluteValue K ℝ→ℝ)
    (u : InfinitePlace K→ℝ) (f : Plane×Plane → CoordinateLevel M.Label → ℝ) :
    M.edgeMean (fun e => M.placeIntegral F l h u (f e)) =
      M.placeIntegral F l h u (fun r => M.edgeMean (fun e => f e r)) := by
  have eq : (fun r => M.edgeMean (fun e => f e r)) =
      ∑e : M.E, (1/(M.E.card:ℝ)) • f e.val := by
    funext r
    simp [edgeMean,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [eq,←placeLinear_apply,map_sum]
  simp only [map_smul,smul_eq_mul,placeLinear_apply,edgeMean]

/-- The endpoint and inconsistency averages required by geometric truncation,
on the same field labels and on the same edge law. -/
theorem arithmetic_tail_means (M : IncidencePiece K) (hS : (2:ℝ)^2100<M.scale)
    (F : Finset (FinitePlace K)) (l h : AbsoluteValue K ℝ→ℝ) (u : InfinitePlace K→ℝ)
    (d : CoordinateLevel M.Label→M.Label)
    (hv : ∀r,M.goodRare r → M.pointMass (fun p => r.selected p≠d r)+M.centerMass (fun q => r.selected q≠d r)
       ≤2*(M.minorityMass r+M.inconsistentMass r))
    (hmin : M.placeIntegral F l h u M.minorityMass=M.scale)
    (hbad : M.placeIntegral F l h u M.inconsistentMass≤2*sqrt 2) :
    let X := M.vertexWidth F l h u d
    let m := M.inconsistentLength F l h u
    (∀p,0≤X p) ∧ (∀e,0≤m e) ∧ M.edgeMean (fun e => X e.1)≤4*M.scale ∧
    M.edgeMean (fun e => X e.2)≤4*M.scale ∧ M.edgeMean m≤4 := by
  let X := M.vertexWidth F l h u d
  let m := M.inconsistentLength F l h u
  have zero : M.placeIntegral F l h u (0 : CoordinateLevel M.Label→ℝ)=0 :=
    (placeLinear_apply M F l h u 0).symm.trans (map_zero _)
  have X0 (p : Plane) : 0≤X p := by
    rw [←zero]; apply placeIntegral_mono M F l h u
    intro r
    change 0≤M.endpointWidth d p r
    by_cases h1 : M.goodRare r <;> by_cases h2 : r.selected p=d r <;>
      simp [endpointWidth,masked,CoordinateLevel.exceptionAt,h1,h2]
  have m0 (e : Plane×Plane) : 0≤m e := by
    rw [←zero]; apply placeIntegral_mono M F l h u
    intro r
    split_ifs <;> norm_num
  have grad (f : Plane×Plane → CoordinateLevel M.Label → ℝ)
      (hf : ∀r,M.edgeMean (fun e => f e r) ≤ 2*(M.minorityMass r+M.inconsistentMass r)) :
      M.edgeMean (fun e => M.placeIntegral F l h u (f e))≤4*M.scale := by
    rw [edgeMean_placeIntegral]
    have b := M.placeIntegral_mono F l h u hf
    have id : (fun r : CoordinateLevel M.Label => 2*(M.minorityMass r+M.inconsistentMass r)) =
        (2:ℝ) • (M.minorityMass+M.inconsistentMass) := rfl
    have lin : M.placeIntegral F l h u (fun r => 2*(M.minorityMass r+M.inconsistentMass r)) =
        2*(M.scale+M.placeIntegral F l h u M.inconsistentMass) := by
      rw [id,←placeLinear_apply M F l h u ((2:ℝ) • (M.minorityMass+M.inconsistentMass)),
        map_smul,map_add,smul_eq_mul,placeLinear_apply,placeLinear_apply,hmin]
    rw [lin] at b
    have small : 2*sqrt 2≤4 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),sq_nonneg (sqrt 2-2)]
    have hs : 4≤M.scale := (show (4:ℝ)=2^2 by norm_num).trans_le
      ((pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by decide : (2:ℕ)≤2100)).trans hS.le)
    exact b.trans ((mul_le_mul_of_nonneg_left (add_le_add le_rfl (hbad.trans (small.trans hs)))
      (by norm_num : (0:ℝ)≤2)).trans_eq (show 2*(M.scale+M.scale)=4*M.scale by ring))
  have widthEvent (k : Plane×Plane → Plane) (r : CoordinateLevel M.Label) :
      M.edgeMean (fun e => M.endpointWidth d (k e) r) =
        if M.goodRare r then M.edgeProb (fun e => r.selected (k e)≠d r) else 0 := by
    by_cases h : M.goodRare r
    · rw [ite_eq_left h,←edgeMean_indicator]
      apply congrArg M.edgeMean; funext e
      by_cases z : r.selected (k e)=d r <;> simp [endpointWidth,masked,h,CoordinateLevel.exceptionAt,z]
    · simp [endpointWidth,masked,h,edgeMean]
  have both (r : CoordinateLevel M.Label) : 0≤2*(M.minorityMass r+M.inconsistentMass r) := by
    unfold minorityMass inconsistentMass edgeProb; positivity
  have hX : M.edgeMean (fun e => X e.1)≤4*M.scale := by
    apply grad (fun e => M.endpointWidth d e.1)
    intro r; rw [widthEvent Prod.fst r]; split_ifs with z
    · rw [edgeProb_point_event M (fun p => r.selected p≠d r)]
      have hz : 0≤M.centerMass (fun q => r.selected q≠d r) := by rw [←edgeProb_center_event]; unfold edgeProb; positivity
      exact (le_add_of_nonneg_right hz).trans (hv r z)
    · exact both r
  have hY : M.edgeMean (fun e => X e.2)≤4*M.scale := by
    apply grad (fun e => M.endpointWidth d e.2)
    intro r; rw [widthEvent Prod.snd r]; split_ifs with z
    · rw [edgeProb_center_event M (fun q => r.selected q≠d r)]
      have hz : 0≤M.pointMass (fun p => r.selected p≠d r) := by rw [←edgeProb_point_event]; unfold edgeProb; positivity
      exact (le_add_of_nonneg_left hz).trans (hv r z)
    · exact both r
  have hm : M.edgeMean m≤4 := by
    have integ := M.edgeMean_placeIntegral F l h u (fun e (r : CoordinateLevel M.Label) => if ¬r.consistent e then (1:ℝ) else 0)
    change M.edgeMean m = _ at integ
    calc
      M.edgeMean m = M.placeIntegral F l h u (fun r => M.edgeMean (fun e => if ¬r.consistent e then (1:ℝ) else 0)) := integ
      _ = M.placeIntegral F l h u M.inconsistentMass := by
        apply congrArg (M.placeIntegral F l h u); funext r
        apply Eq.trans _ (M.edgeMean_indicator (fun e => ¬r.consistent e))
        apply congrArg M.edgeMean; funext e
        by_cases z : r.consistent e <;> simp [z]
      _ ≤ 4 := hbad.trans (by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),sq_nonneg (sqrt 2-2)])
  exact ⟨X0,m0,hX,hY,hm⟩

end
end PlanarUnitDistances.Competition.IncidencePiece

