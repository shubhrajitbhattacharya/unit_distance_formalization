import PlanarUnitDistances.GridElimination
import PlanarUnitDistances.AnchorNormalization

/-! Cartesian geometry of a solution of the 140 enumerated lifted equations
over an arbitrary field extending the complex numbers. -/
namespace PlanarUnitDistances.Competition.LiftedTangent
open MvPolynomial GridElimination
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

def nullPos (y : LiftCoord → E) (s : Slot) (d : Fin 2) : E := y (.inl (s,d))
def cart (y : LiftCoord → E) (s : Slot) : Fin 2 → E :=
  ![algebraMap ℂ E (1/2)*(nullPos y s 0 + nullPos y s 1),
    algebraMap ℂ E (1/(2*Complex.I))*(nullPos y s 0 - nullPos y s 1)]
def u (y : LiftCoord → E) (i : Fin 8) (j : Fin 4) : E := y (.inr (.inl ((i,j),0)))
def μ (y : LiftCoord → E) (i : Fin 8) (j : Fin 4) : E := y (.inr (.inl ((i,j),1)))
def H (y : LiftCoord → E) (i : Fin 8) (d : Fin 2) : E := y (.inr (.inr (.inl i,d.castSucc)))
def U (y : LiftCoord → E) (j : Fin 4) (d : Fin 2) : E := y (.inr (.inr (.inr j,d.castSucc)))
def A (y : LiftCoord → E) (i : Fin 8) : E := y (.inr (.inr (.inl i,2)))
def a (y : LiftCoord → E) (j : Fin 4) : E := y (.inr (.inr (.inr j,2)))

/-- Recover both original null coordinates from the Cartesian entries, with
the sign convention used by the defining equations. -/
theorem recover (y : LiftCoord → E) (s : Slot) :
    cart y s 0 + algebraMap ℂ E Complex.I * cart y s 1 = nullPos y s 0 ∧
    cart y s 0 - algebraMap ℂ E Complex.I * cart y s 1 = nullPos y s 1 := by
  have hi := (algebraMap ℂ E).injective.ne Complex.I_ne_zero
  simp only [map_zero] at hi
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℂ E).injective
  simp only [cart,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    map_div₀,map_mul,map_one,map_ofNat]
  constructor <;> field_simp [hi] <;> ring

private theorem indexed_edges (y : LiftCoord → E) (hedge : ∀ k, aeval y (edgeList k)=0)
    (i : Fin 8) (j : Fin 4) (h : Fin 4) : aeval y (edgeEquation i j h) = 0 := by
  let e := (Fintype.equivFinOfCardEq (α := Edge × Fin 4) (n := 128) (by simp [Edge])).symm
  obtain ⟨k,hk⟩ := e.surjective ((i,j),h)
  have Hk := hedge k
  change aeval y (edgeEquation (e k).1.1 (e k).1.2 (e k).2) = 0 at Hk
  simpa only [hk] using Hk

private theorem indexed_curves (f g : Poly₂) (y : LiftCoord → E)
    (hcurve : ∀ k, aeval y (curveList f g k)=0) (s : Slot) :
    aeval (nullPos y s) (s.elim (fun _ ↦ f) (fun _ ↦ g)) = 0 := by
  let e := (Fintype.equivFinOfCardEq (α := Slot) (n := 12) (by decide)).symm
  obtain ⟨k,hk⟩ := e.surjective s
  have Hk := hcurve k
  change aeval y (curveEquation f g (e k))=0 at Hk
  rw [hk] at Hk
  have obs : (y ∘ fun d : Fin 2 ↦ (Sum.inl (s,d) : LiftCoord)) = nullPos y s := by
    funext d
    rfl
  rw [curveEquation,aeval_rename,obs] at Hk
  exact Hk

def chordSq (y : LiftCoord → E) (i : Fin 8) (j : Fin 4) : E :=
  (cart y (.inl i) 0 - cart y (.inr j) 0)^2 + (cart y (.inl i) 1 - cart y (.inr j) 1)^2

theorem chordSq_eq_null (y : LiftCoord → E) (i : Fin 8) (j : Fin 4) :
    chordSq y i j = (nullPos y (.inl i) 0-nullPos y (.inr j) 0) *
      (nullPos y (.inl i) 1-nullPos y (.inr j) 1) := by
  obtain ⟨p0,p1⟩ := recover y (.inl i)
  obtain ⟨r0,r1⟩ := recover y (.inr j)
  have hI : (algebraMap ℂ E Complex.I)^2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  rw [←p0,←p1,←r0,←r1]
  unfold chordSq
  linear_combination (cart y (.inl i) 1-cart y (.inr j) 1)^2*hI

/-- Complete tangent and chord data on the unchanged lifted field point.
The scalar (μ−u) is the radical for the four-anchor determinant. -/
structure Data (f g : Poly₂) (y : LiftCoord → E) : Prop where
  compatible : GenericParameters.Compatible (fun i ↦ cart y (.inl i)) (fun j ↦ cart y (.inr j))
    (fun i j ↦ μ y i j-u y i j) (H y) (U y) (A y) (a y)
  inverse : ∀ i j, u y i j * μ y i j = 1
  chord : ∀ i j, chordSq y i j = 2-u y i j-μ y i j
  radical : ∀ i j, (μ y i j-u y i j)^2 = chordSq y i j*(chordSq y i j-4)
  row_curve : ∀ i, aeval (nullPos y (.inl i)) f = 0
  anchor_curve : ∀ j, aeval (nullPos y (.inr j)) g = 0

theorem data_of_lift (f g : Poly₂) (y : LiftCoord → E)
    (hedge : ∀ k, aeval y (edgeList k)=0) (hcurve : ∀ k, aeval y (curveList f g k)=0) :
    Data f g y := by
  have two : algebraMap ℂ E 2 = 2 := map_ofNat _ _
  have iv (i : Fin 8) (j : Fin 4) : u y i j * μ y i j = 1 := by
    simpa [u,μ,edgeEquation,edgeVar,sub_eq_zero] using indexed_edges y hedge i j 0
  have chord (i : Fin 8) (j : Fin 4) : chordSq y i j = 2-u y i j-μ y i j := by
    rw [chordSq_eq_null]
    simpa [edgeEquation,dw,point,edgeVar,nullPos,u,μ,sub_eq_zero,two] using indexed_edges y hedge i j 1
  refine ⟨?_,iv,chord,?_,fun i ↦ indexed_curves f g y hcurve (.inl i),
    fun j ↦ indexed_curves f g y hcurve (.inr j)⟩
  · intro i j
    have deriv := indexed_edges y hedge i j 2
    have distinct := indexed_edges y hedge i j 3
    simp [edgeEquation,edgeVar,dw,dv,point,velocity,sub_eq_zero,two] at deriv distinct
    refine ⟨?_,sub_ne_zero.mp (right_ne_zero_of_mul_eq_one distinct)⟩
    simp [cart,nullPos,u,μ,U,H,A,a,two] 
    linear_combination deriv
  · intro i j
    rw [chord]
    linear_combination -4 * iv i j

end
end PlanarUnitDistances.Competition.LiftedTangent

