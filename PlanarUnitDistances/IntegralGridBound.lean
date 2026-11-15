import PlanarUnitDistances.IntegralSubstitutionSize

namespace PlanarUnitDistances.IntegralGrid
open MvPolynomial EliminantHeight
noncomputable section
variable {U V W : Type*}

abbrev Labels (U : Type*) := MvPolynomial U ℤ
abbrev InStates (U V : Type*) := MvPolynomial V (Labels U)

/-- Every state coefficient is affine linear in all label slots jointly,
with the indicated upper bound on the sum of absolute integer coefficients. -/
def Bound (n : ℕ) (f : InStates U V) : Prop :=
  ∀ d, (f.coeff d).totalDegree ≤ 1 ∧ coefficientSum (f.coeff d) ≤ n

private theorem zero_cost : coefficientSum (0 : Labels U)=0 := by simp [coefficientSum]

theorem label_cost (u : U) : coefficientSum (X u : Labels U) = 1 := by
  change coefficientSum (monomial (Finsupp.single u 1) (1:ℤ)) = 1
  simp

private theorem neg_cost (f : Labels U) : coefficientSum (-f) = coefficientSum f := by
  classical
  simp [coefficientSum, MvPolynomial.support_neg]

theorem Bound.mono {n m : ℕ} {p : InStates U V} (hp : Bound n p) (h : n ≤ m) : Bound m p :=
  fun d => ⟨(hp d).1,(hp d).2.trans h⟩

theorem Bound.C {n : ℕ} {c : Labels U} (h : c.totalDegree ≤ 1) (s : coefficientSum c ≤ n) :
    Bound n (MvPolynomial.C c : InStates U V) := by
  classical
  intro d
  rw [coeff_C]
  split_ifs
  · exact ⟨h,s⟩
  · simp [zero_cost]

theorem Bound.one : Bound 1 (1 : InStates U V) := by
  simpa only [map_one] using Bound.C (V:=V) (c:=(1 : Labels U)) (by simp) (by simp)

theorem Bound.X (v : V) : Bound 1 (MvPolynomial.X v : InStates U V) := by
  classical
  intro d
  rw [coeff_X]
  split_ifs <;> simp [zero_cost]

theorem Bound.mul_X {n : ℕ} {p : InStates U V} (h : Bound n p) (v : V) :
    Bound n (p*MvPolynomial.X v) := by
  classical
  intro d
  rw [coeff_mul_X']
  split_ifs
  · exact h _
  · simp [zero_cost]

theorem Bound.add {n m : ℕ} {p q : InStates U V} (h : Bound n p) (g : Bound m q) :
    Bound (n+m) (p+q) := by
  intro d
  rw [MvPolynomial.coeff_add]
  exact ⟨(totalDegree_add ..).trans (max_le (h d).1 (g d).1),
    (coefficientSum_add_le ..).trans (Nat.add_le_add (h d).2 (g d).2)⟩

theorem Bound.sub {n m : ℕ} {p q : InStates U V} (h : Bound n p) (g : Bound m q) :
    Bound (n+m) (p-q) := by
  rw [sub_eq_add_neg]
  apply h.add
  intro d
  simpa only [coeff_neg, totalDegree_neg,neg_cost] using g d

theorem Bound.rename {n : ℕ} {p : InStates U V} (h : Bound n p) (v : V → W) (hv : Function.Injective v) :
    Bound n (MvPolynomial.rename v p) := by
  intro d
  by_cases hz : (MvPolynomial.rename v p).coeff d = 0
  · simp [hz,zero_cost]
  obtain ⟨a,rfl,_⟩ := coeff_rename_ne_zero v p d hz
  rw [coeff_rename_mapDomain v hv]
  exact h a

theorem Bound.sum {B : Type*} {n : ℕ} (S : Finset B) (p : B → InStates U V) (hs : ∀ i, Bound n (p i)) :
    Bound (S.card*n) (∑ i ∈ S, p i) := by
  classical
  induction S using Finset.induction_on with
  | empty => intro d; simp [zero_cost]
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.add_mul, one_mul, Nat.add_comm]
    exact (hs i).add ih

theorem Bound.pderiv {n : ℕ} {p : InStates U V} (h : Bound n p) (hd : p.totalDegree ≤ 2) (i : V) :
    Bound (2*n) (MvPolynomial.pderiv i p) := by
  classical
  intro d
  rw [coeff_pderiv]
  by_cases hz : p.coeff (d+Finsupp.single i 1) = 0
  · simp [hz,zero_cost]
  have hm := (le_degreeOf_of_mem_support i (mem_support_iff.mpr hz)).trans ((degreeOf_le_totalDegree p i).trans hd)
  simp at hm
  have hd' : d i = 0 ∨ d i = 1 := by omega
  let b := p.coeff (d+Finsupp.single i 1)
  obtain ⟨deg,cost⟩ := h (d+Finsupp.single i 1)
  rcases hd' with zero | one
  · simpa [zero] using (show b.totalDegree ≤ 1 ∧ coefficientSum b ≤ 2*n from ⟨deg,by dsimp [b]; omega⟩)
  · rw [one]
    change (b*(1+1)).totalDegree ≤ 1 ∧ coefficientSum (b*(1+1)) ≤ 2*n
    rw [mul_add,mul_one]
    exact ⟨(totalDegree_add ..).trans (max_le deg deg), (coefficientSum_add_le ..).trans (by dsimp [b]; omega)⟩

end
end PlanarUnitDistances.IntegralGrid
