import PlanarUnitDistances.RareCoordinateLevels

namespace PlanarUnitDistances.Competition.IncidencePiece
open Finset MeasureTheory
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K] {L : Type*} [Fintype L] [Nonempty L]

def goodRare (M : IncidencePiece K) (r : CoordinateLevel L) : Prop :=
  M.minorityMass r < eps ∧ M.inconsistentMass r ≤ eps

def edgeException (M : IncidencePiece K) (r : CoordinateLevel L) (a : L) :=
  M.edgeProb (fun e => r.selected e.1≠a ∧ r.selected e.2≠a)

def walkException (M : IncidencePiece K) (r : CoordinateLevel L) (a : L) :=
  ∑v : Triple M, if r.selected v.1.val≠a ∧ r.selected v.2.2.val≠a then M.mass v else 0

/-- The selected label depends only on the complete record. The same
choice therefore works for every measure on levels and at every place. -/
theorem recordwise_rare (M : IncidencePiece K) {t : ℝ} (reg : Regular M t) (ht : 0<t)
    (hx : t^(-150*savingG)≤(2:ℝ)^(-154:ℝ)) :
    ∃ d : CoordinateLevel L → L, ∀r,M.goodRare r →
      M.pointMass (fun p => r.selected p≠d r)+M.centerMass (fun q => r.selected q≠d r)
          ≤2*(M.minorityMass r+M.inconsistentMass r) ∧
      M.edgeException r (d r) ≤ (5*(2:ℝ)^(-144:ℝ)/2)*(M.minorityMass r+M.inconsistentMass r) ∧
      M.walkException r (d r) ≤ ((2:ℝ)^(-144:ℝ)/2)*(M.minorityMass r+M.inconsistentMass r) := by
  let C (r : CoordinateLevel L) (a : L) := M.goodRare r →
    M.pointMass (fun p => r.selected p≠a)+M.centerMass (fun q => r.selected q≠a)
      ≤2*(M.minorityMass r+M.inconsistentMass r) ∧
    M.edgeException r a≤(5*(2:ℝ)^(-144:ℝ)/2)*(M.minorityMass r+M.inconsistentMass r) ∧
    M.walkException r a≤((2:ℝ)^(-144:ℝ)/2)*(M.minorityMass r+M.inconsistentMass r)
  change ∃d : CoordinateLevel L → L,∀r,C r (d r)
  apply Classical.axiomOfChoice (r:=C)
  intro r
  by_cases good : M.goodRare r
  · let ν := Measure.dirac ()
    let R : SimpleFunc Unit ((Plane → L)×(Plane → L)) := SimpleFunc.const Unit (r.selected,r.selected)
    let h := M.minorityMass r+M.inconsistentMass r
    have prob (A : Plane×Plane → Prop) : 0≤M.edgeProb A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h0 : 0≤h := add_nonneg (prob _) (prob _)
    have hs (s : Unit) : M.labelMismatch (R s)≤2*eps :=
      (majority_mismatch M r).trans ((add_le_add good.1.le good.2).trans_eq (two_mul eps).symm)
    have hw : (∫s,M.labelMismatch (R s) ∂ν)≤2*(h/2) := by
      rw [integral_dirac,show 2*(h/2)=h by ring]
      exact majority_mismatch M r
    obtain ⟨a,ha,he,hw'⟩ := rare_edge_and_walk ν M reg ht (div_nonneg h0 (by norm_num : (0:ℝ)≤2)) hx R hs hw
    rw [integral_dirac] at he hw'
    refine ⟨a (),fun _ => ⟨(ha ()).trans (mul_le_mul_of_nonneg_left (majority_mismatch M r) (by norm_num)),?_,?_⟩⟩
    · exact he.trans_eq (by unfold h; ring)
    · exact hw'.trans_eq (by unfold h; ring)
  · exact ⟨Classical.choice ‹Nonempty L›,fun g => (good g).elim⟩

def masked (M : IncidencePiece K) (f : CoordinateLevel L → ℝ) (r : CoordinateLevel L) :=
  if M.goodRare r then f r else 0

omit [Fintype L] [Nonempty L] in
/-- An explicitly masked integral over an arbitrary finite level interval;
all records, including common and inconsistent levels, may be supplied. -/
theorem integrate_recordwise {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν]
    (M : IncidencePiece K) (R : SimpleFunc Ω (CoordinateLevel L)) (f : CoordinateLevel L → ℝ)
    {c : ℝ} (hc : 0≤c) (bound : ∀r,M.goodRare r → f r≤c*(M.minorityMass r+M.inconsistentMass r)) :
    (∫s,M.masked f (R s) ∂ν)≤c*((∫s,M.minorityMass (R s) ∂ν)+(∫s,M.inconsistentMass (R s) ∂ν)) := by
  have iF : Integrable (fun s => M.minorityMass (R s)) ν := (R.map (minorityMass M)).integrable_of_isFiniteMeasure
  have iM : Integrable (fun s => M.inconsistentMass (R s)) ν := (R.map (inconsistentMass M)).integrable_of_isFiniteMeasure
  rw [←integral_add iF iM,←integral_const_mul]
  apply integral_mono (R.map (M.masked f)).integrable_of_isFiniteMeasure ((iF.add iM).const_mul c)
  intro s
  by_cases hg : M.goodRare (R s)
  · exact (ite_eq_left hg).trans_le (bound _ hg)
  · apply (ite_eq_right hg).trans_le
    apply mul_nonneg hc
    exact add_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

end
end PlanarUnitDistances.Competition.IncidencePiece
