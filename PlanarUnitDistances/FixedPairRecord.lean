import PlanarUnitDistances.LocalEndpoint

namespace PlanarUnitDistances.Competition.IncidencePiece
open Real
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

/-- The manuscript's rare positive term for base p and its two indicated
neighbors. On the common minority bit the tested neighbor coordinate is the
coordinate selected by the majority. -/
def rarePairPositive (M : IncidencePiece K) (d : CoordinateLevel M.Label → M.Label)
    (p q q' : Plane) (r : CoordinateLevel M.Label) : ℝ :=
  if M.goodRare r ∧ r.selected p≠d r ∧ r.bit (p,q)≠r.majority ∧
      r.bit (p,q')≠r.majority ∧ r.selected q=r.selected q' then 2 else 0

def rarePairScore (M : IncidencePiece K) (d : CoordinateLevel M.Label → M.Label)
    (p q q' : Plane) (r : CoordinateLevel M.Label) : ℝ :=
  M.rarePairPositive d p q q' r - |bitValue (r.bit (p,q))-bitValue (r.bit (p,q'))|

private theorem edge_bit_iff {L : Type} (r : CoordinateLevel L) {p q : Plane}
    (h : r.consistent (p,q)) : r.bit (p,q)=r.majority ↔ r.selected p=r.selected q := by
  cases hb : r.bit (p,q) <;> cases hm : r.majority <;>
    simp [CoordinateLevel.consistent,CoordinateLevel.selected,hb,hm] at h ⊢ <;> tauto

/-- The pointwise rare lower bound, prior to integration or the product
formula. It includes both inconsistency flags and all excluded levels. -/
theorem rare_pair_lower_record (M : IncidencePiece K) (d : CoordinateLevel M.Label → M.Label)
    (p q q' : Plane) (r : CoordinateLevel M.Label) :
    2*M.endpointWidth d p r ≤
     3*(M.endpointWidth d q r+M.endpointWidth d q' r+r.errorAt (p,q)+r.errorAt (p,q'))+
       M.rarePairScore d p q q' r+(if M.goodRare r then 0 else 1) := by
  have hbit : |bitValue (r.bit (p,q))-bitValue (r.bit (p,q'))| ≤ 1 := by
    cases h1 : r.bit (p,q) <;> cases h2 : r.bit (p,q') <;> norm_num [bitValue]
  have err (e : Plane×Plane) : 0 ≤ r.errorAt e := by unfold CoordinateLevel.errorAt; split <;> norm_num
  by_cases good : M.goodRare r
  · simp only [endpointWidth,masked,ite_eq_left good,add_zero,rarePairScore]
    have non (x : Plane) : 0≤r.exceptionAt (d r) x := by unfold CoordinateLevel.exceptionAt; split <;> norm_num
    have maxp : r.exceptionAt (d r) p≤1 := by unfold CoordinateLevel.exceptionAt; split <;> norm_num
    have plus : 0≤M.rarePairPositive d p q q' r := by unfold rarePairPositive; split <;> norm_num
    by_cases clean : r.selected q=d r ∧ r.selected q'=d r ∧ r.consistent (p,q) ∧ r.consistent (p,q')
    · obtain ⟨hq,hq',c,c'⟩ := clean
      have eq1 := edge_bit_iff r c
      have eq2 := edge_bit_iff r c'
      rw [hq] at eq1; rw [hq'] at eq2
      have same : r.bit (p,q)=r.bit (p,q') := by
        cases z : r.majority <;> cases b : r.bit (p,q) <;> cases b' : r.bit (p,q') <;> simp_all
      by_cases hp : r.selected p=d r
      · simp only [same,sub_self,abs_zero,sub_zero]
        simp [rarePairPositive,CoordinateLevel.exceptionAt,hp,hq,hq',CoordinateLevel.errorAt,c,c']
      · have b1 := (not_congr eq1).mpr hp
        have b2 := (not_congr eq2).mpr hp
        simp only [same,sub_self,abs_zero,sub_zero]
        norm_num [rarePairPositive,CoordinateLevel.exceptionAt,hp,hq,hq',CoordinateLevel.errorAt,c,c',good,b1,b2]
    · have unit : 1≤r.exceptionAt (d r) q +r.exceptionAt (d r) q'+r.errorAt (p,q)+r.errorAt (p,q') := by
        by_cases h1 : r.selected q=d r <;> by_cases h2 : r.selected q'=d r <;>
          by_cases h3 : r.consistent (p,q) <;> by_cases h4 : r.consistent (p,q') <;>
          simp_all [CoordinateLevel.exceptionAt,CoordinateLevel.errorAt] <;> norm_num
      linarith only [unit,hbit,maxp,plus]
  · simp only [endpointWidth,masked,ite_eq_right good,zero_add,mul_zero,rarePairScore]
    simp only [rarePairPositive,good,false_and,ite_false,zero_sub]
    linarith only [hbit,err (p,q),err (p,q')]

end
end PlanarUnitDistances.Competition.IncidencePiece

