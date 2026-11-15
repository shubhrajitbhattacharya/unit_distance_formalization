import PlanarUnitDistances.IntegralGridBound
import PlanarUnitDistances.TorusParameterEliminants

namespace PlanarUnitDistances.IntegralGrid
open MvPolynomial EliminantHeight
open TorusCritical (Coord Equation RatioParameters ratioParameterValues)
noncomputable section
variable {I J : Type*}
abbrev State (I J : Type*) := InStates (RatioParameters I J) (Coord I J)

def colUnit (j : Option J) (h : Fin 2) : State I J :=
  j.elim 1 (fun s ↦ X (.inr (.inr (s, h))))

def positionDifference (i : I) (j : Option J) (h : Fin 2) : State I J :=
  X (.inl (i, h.castLE (by decide))) - X (.inr (.inl (j, h)))

def ratio (i : I) (j : Option J) : State I J :=
  C (X ((i,j),false)) * X (.inl (i, 2)) * colUnit j 0

def inverseRatio (i : I) (j : Option J) : State I J :=
  C (X ((i,j),true)) * X (.inl (i, 3)) * colUnit j 1

def equation : Equation I J → State I J
  | .inl i => X (.inl (i, 2)) * X (.inl (i, 3)) - 1
  | .inr (.inl j) => colUnit (some j) 0 * colUnit (some j) 1 - 1
  | .inr (.inr (i,j)) => positionDifference i j 0 ^ 2 + positionDifference i j 1 ^ 2
      - C (2 : Labels (RatioParameters I J)) + ratio i j + inverseRatio i j

private theorem colUnit_degree (j : Option J) (h : Fin 2) :
    (colUnit (I := I) (J := J) j h).totalDegree ≤ 1 := by
  cases j <;> simp [colUnit]

private theorem positionDifference_degree (i : I) (j : Option J) (h : Fin 2) :
    (positionDifference i j h).totalDegree ≤ 1 := by
  exact (totalDegree_sub _ _).trans (by simp)

private theorem term_degree (a : Labels (RatioParameters I J)) (u : Coord I J) (j : Option J) (h : Fin 2) :
    (C a * X u * colUnit j h).totalDegree ≤ 2 := by
  apply (totalDegree_mul _ _).trans
  have h1 := totalDegree_mul (C a) (X u)
  rw [totalDegree_C, totalDegree_X] at h1
  have h2 := colUnit_degree (I := I) (J := J) j h
  omega

theorem ratio_degree (i : I) (j : Option J) :
    (ratio i j).totalDegree ≤ 2 :=
  term_degree _ _ _ _

theorem equation_degree (e : Equation I J) :
    (equation e).totalDegree ≤ 2 := by
  rcases e with i | (j | ⟨i,j⟩)
  · apply (totalDegree_sub _ _).trans
    apply max_le _ (by simp)
    exact (totalDegree_mul _ _).trans (by simp)
  · apply (totalDegree_sub _ _).trans
    apply max_le _ (by simp)
    exact (totalDegree_mul _ _).trans (by simp [colUnit])
  · have hs (h : Fin 2) : (positionDifference i j h ^ 2).totalDegree ≤ 2 :=
      (totalDegree_pow _ _).trans (by have := positionDifference_degree i j h; omega)
    apply (totalDegree_add _ _).trans (max_le _ (term_degree _ _ _ _))
    apply (totalDegree_add _ _).trans (max_le _ (ratio_degree i j))
    apply (totalDegree_sub _ _).trans (max_le _ (by simp))
    exact (totalDegree_add _ _).trans (max_le (hs 0) (hs 1))


private theorem square_bound {U V : Type*} (x y : V) :
    Bound 4 ((X x-X y : InStates U V)^2) := by
  let px := (X x : InStates U V)
  let py := (X y : InStates U V)
  have eq : (px-py)^2 = (px*px-px*py)+(py*py-py*px) := by ring
  rw [show (X x-X y : InStates U V)^2 = _ from eq]
  exact (((Bound.X x).mul_X x).sub ((Bound.X x).mul_X y)).add
    (((Bound.X y).mul_X y).sub ((Bound.X y).mul_X x))

private theorem labelled_term (u : RatioParameters I J) (i : Coord I J) (j : Option J) (t : Fin 2) :
    Bound 1 (C (X u) * X i * colUnit j t : State I J) := by
  have h := (Bound.C (V:=Coord I J) (c:=(X u:Labels (RatioParameters I J))) (by simp) (label_cost u).le).mul_X i
  cases j with
  | none => simpa [colUnit] using h
  | some j => exact h.mul_X _

theorem ratio_bound (i : I) (j : Option J) : Bound 1 (ratio i j) := labelled_term _ _ _ _

theorem equation_bound (e : Equation I J) : Bound 12 (equation e) := by
  have hone : Bound 1 (1 : State I J) := Bound.one
  have htwo : Bound 2 (C (2 : Labels (RatioParameters I J)) : State I J) := by
    rw [show (C (2 : Labels (RatioParameters I J)) : State I J)=1+1 by rw [show (2 : Labels (RatioParameters I J))=1+1 by ring,map_add,C_1]]
    exact hone.add hone
  rcases e with i | (j | ⟨i,j⟩)
  · exact (((Bound.X _).mul_X _).sub hone).mono (by decide)
  · exact (((Bound.X _).mul_X _).sub hone).mono (by decide)
  · exact ((((square_bound _ _).add (square_bound _ _)).sub htwo).add (ratio_bound i j)).add (labelled_term _ _ _ _)

variable {k : Type*} [Field k]
def atLabels (a : I → Option J → kˣ) : Labels (RatioParameters I J) →+* k :=
  eval₂Hom (Int.castRingHom k) (ratioParameterValues a)

@[simp] theorem atLabels_X (a : I → Option J → kˣ) (t : RatioParameters I J) :
    atLabels a (X t) = ratioParameterValues a t := by simp [atLabels]

theorem map_colUnit (a : I → Option J → kˣ) (j : Option J) (h : Fin 2) :
    MvPolynomial.map (atLabels a) (colUnit (I:=I) j h) = TorusCritical.colUnit j h := by
  cases j <;> simp [colUnit,TorusCritical.colUnit]

theorem map_position (a : I → Option J → kˣ) (i : I) (j : Option J) (h : Fin 2) :
    MvPolynomial.map (atLabels a) (positionDifference i j h) = TorusCritical.positionDifference i j h := by
  simp [positionDifference,TorusCritical.positionDifference]

theorem map_ratio (a : I → Option J → kˣ) (i : I) (j : Option J) :
    MvPolynomial.map (atLabels a) (ratio i j) = TorusCritical.ratio a i j := by
  simp [ratio,TorusCritical.ratio,ratioParameterValues,map_colUnit]

theorem map_equation (a : I → Option J → kˣ) (e : Equation I J) :
    MvPolynomial.map (atLabels a) (equation e) = TorusCritical.equation a e := by
  rcases e with i | (j | ⟨i,j⟩) <;>
    simp [equation,TorusCritical.equation,map_position,map_colUnit,map_ratio,inverseRatio,
      TorusCritical.inverseRatio,ratioParameterValues]
  rw [show (2 : Labels (RatioParameters I J))=1+1 by ring,map_add,map_one,one_add_one_eq_two]

end
end PlanarUnitDistances.IntegralGrid
