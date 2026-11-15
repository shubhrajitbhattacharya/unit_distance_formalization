import PlanarUnitDistances.RareCoordinateLevels

namespace PlanarUnitDistances.Competition.IncidencePiece
open scoped Classical
noncomputable section
variable {L : Type*}

def bitValue (b : Bool) : ℝ := if b then 1 else 0
def CoordinateLevel.exceptionAt (r : CoordinateLevel L) (a : L) (p : Plane) : ℝ := if r.selected p=a then 0 else 1
def CoordinateLevel.errorAt (r : CoordinateLevel L) (e : Plane×Plane) : ℝ := if r.consistent e then 0 else 1
def CoordinateLevel.bitSign (r : CoordinateLevel L) : ℝ := 1-2*bitValue r.majority
open CoordinateLevel

private lemma equal_labels (r : CoordinateLevel L) (e : Plane×Plane) (hc : r.consistent e) :
    r.selected e.1=r.selected e.2 ↔ r.bit e=r.majority := by
  cases hb : r.bit e <;> cases hm : r.majority <;>
    simp_all [CoordinateLevel.selected,CoordinateLevel.consistent]

/-- The rare-level comparison for one original edge. The only charged
exceptions are a simultaneous exceptional point and center, or an
inconsistent edge. The center term will cancel when subtracting edges. -/
theorem edge_error (r : CoordinateLevel L) (a : L) (e : Plane×Plane) :
    |bitValue (r.bit e)-bitValue r.majority-r.bitSign*(r.exceptionAt a e.1+r.exceptionAt a e.2)|
      ≤ 2*(r.exceptionAt a e.1*r.exceptionAt a e.2+r.errorAt e) := by
  by_cases c : r.consistent e
  · have h := equal_labels r e c
    cases hb : r.bit e <;> cases hm : r.majority <;>
      by_cases p : r.selected e.1=a <;> by_cases q : r.selected e.2=a <;>
      simp_all [bitValue,bitSign,exceptionAt,errorAt] <;> norm_num
  · cases hb : r.bit e <;> cases hm : r.majority <;>
      by_cases p : r.selected e.1=a <;> by_cases q : r.selected e.2=a <;>
      norm_num [bitValue,bitSign,exceptionAt,errorAt,hb,hm,p,q,c]

def CoordinateLevel.twoEdgeError (r : CoordinateLevel L) (a : L) (p q x : Plane) :=
  2*(r.exceptionAt a p*r.exceptionAt a q+r.exceptionAt a x*r.exceptionAt a q+r.errorAt (p,q)+r.errorAt (x,q))

/-- Both incidences use exactly the same center, record, sign and label. -/
theorem subtract_edges (r : CoordinateLevel L) (a : L) (p q x : Plane) :
    |(bitValue (r.bit (p,q))-bitValue (r.bit (x,q)))-r.bitSign*(r.exceptionAt a p-r.exceptionAt a x)|
       ≤ r.twoEdgeError a p q x := by
  have hp := abs_le.mp (edge_error r a (p,q))
  have hx := abs_le.mp (edge_error r a (x,q))
  dsimp only at hp hx
  unfold twoEdgeError
  exact abs_le.mpr ⟨by linarith only [hp.1,hx.2],by linarith only [hp.2,hx.1]⟩

/-- The lower estimate for the unsigned disagreement on a single level
charges an additional two units precisely when both points are exceptional. -/
theorem subtract_edges_unsigned (r : CoordinateLevel L) (a : L) (p q x : Plane) :
    r.exceptionAt a p+r.exceptionAt a x-2*r.exceptionAt a p*r.exceptionAt a x-r.twoEdgeError a p q x
    ≤ |bitValue (r.bit (p,q))-bitValue (r.bit (x,q))| := by
  have j := subtract_edges r a p q x
  let d := bitValue (r.bit (p,q))-bitValue (r.bit (x,q))
  let b := r.bitSign*(r.exceptionAt a p-r.exceptionAt a x)
  have rev : |b|≤|d|+|d-b| := by
    calc
      _ = |d+(b-d)| := by ring_nf
      _ ≤ _ := (abs_add_le ..).trans_eq (by rw [abs_sub_comm b d])
  have net : r.exceptionAt a p+r.exceptionAt a x-2*r.exceptionAt a p*r.exceptionAt a x=|b| := by
    cases hm : r.majority <;> by_cases hp : r.selected p=a <;> by_cases hx : r.selected x=a <;>
      norm_num [b,bitSign,bitValue,exceptionAt,hm,hp,hx]
  change |d-b|≤_ at j
  change _≤|d|
  linarith only [j,rev,net]

end
end PlanarUnitDistances.Competition.IncidencePiece
