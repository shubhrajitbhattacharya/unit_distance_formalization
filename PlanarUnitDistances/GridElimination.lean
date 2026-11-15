import PlanarUnitDistances.PositionSystem
import PlanarUnitDistances.PublishedElimination

/-! Deep Blue. The 156-coordinate algebraic incidence set for the actual
8-by-4 Cartesian tangent equations expressed in null position coordinates. -/

noncomputable section

namespace PlanarUnitDistances.Competition.GridElimination

open MvPolynomial PublishedElimination

abbrev Edge := Fin 8 × Fin 4
abbrev LiftCoord := Coord ⊕ ((Edge × Fin 3) ⊕ (Slot × Fin 3))
abbrev P := MvPolynomial LiftCoord ℂ

def point (s : Slot) (d : Fin 2) : P := X (.inl (s,d))
def edgeVar (i : Fin 8) (j : Fin 4) (t : Fin 3) : P := X (.inr (.inl ((i,j),t)))
def velocity (s : Slot) (t : Fin 3) : P := X (.inr (.inr (s,t)))
def dw (i : Fin 8) (j : Fin 4) (d : Fin 2) : P := point (.inl i) d-point (.inr j) d
def dv (i : Fin 8) (j : Fin 4) (d : Fin 3) : P := velocity (.inl i) d-velocity (.inr j) d

def edgeEquation (i : Fin 8) (j : Fin 4) : Fin 4 → P :=
  ![edgeVar i j 0*edgeVar i j 1-1,
    dw i j 0*dw i j 1 - (C 2-edgeVar i j 0-edgeVar i j 1),
    C 2*(C (1/2)*(dw i j 0+dw i j 1)*dv i j 0+
      C (1/(2*Complex.I))*(dw i j 0-dw i j 1)*dv i j 1)-
      (edgeVar i j 1-edgeVar i j 0)*dv i j 2,
    edgeVar i j 2*dv i j 2-1]

def curveEquation (f g : Poly₂) (s : Slot) : P :=
  rename (fun d ↦ Sum.inl (s,d)) (s.elim (fun _ ↦ f) (fun _ ↦ g))

private def enumerate {U : Type} [Fintype U] {n : ℕ} (h : Fintype.card U = n) : Fin n ≃ U :=
  (Fintype.equivFinOfCardEq h).symm

def edgeList (i : Fin 128) : P :=
  let e := enumerate (U := Edge × Fin 4) (by simp [Edge]) i
  edgeEquation e.1.1 e.1.2 e.2

def curveList (f g : Poly₂) (i : Fin 12) : P :=
  curveEquation f g (enumerate (U := Slot) (by decide) i)

private theorem all_lift_eqs (f g : Poly₂) (y : LiftCoord → ℂ) :
    y ∈ equations (List.ofFn edgeList ++ List.ofFn (curveList f g)) ↔
    (∀ i j h, eval y (edgeEquation i j h) = 0) ∧ (∀ s, eval y (curveEquation f g s) = 0) := by
  change (∀ F ∈ List.ofFn edgeList ++ List.ofFn (curveList f g), _) ↔ _
  simp only [List.mem_append,List.mem_ofFn]
  constructor
  · rintro h
    constructor
    · intro i j l
      obtain ⟨k,hk⟩ := (enumerate (U := Edge × Fin 4) (n := 128) (by simp [Edge])).surjective ((i,j),l)
      exact h _ (Or.inl ⟨k,by simp [edgeList,hk]⟩)
    · intro s
      obtain ⟨k,hk⟩ := (enumerate (U := Slot) (n := 12) (by decide)).surjective s
      exact h _ (Or.inr ⟨k,by simp [curveList,hk]⟩)
  · rintro ⟨a,b⟩ _ (⟨k,rfl⟩ | ⟨k,rfl⟩)
    · exact a _ _ _
    · exact b _

private theorem curve_eval (f g : Poly₂) (y : LiftCoord → ℂ) :
    (∀ s, eval y (curveEquation f g s) = 0) ↔ (fun i ↦ y (.inl i)) ∈ curveProduct f g := by
  simp only [curveEquation,eval_rename,curveProduct,Set.mem_ofPred_eq,Sum.forall,Sum.elim_inl,Sum.elim_inr]
  rfl


private def packed (x : GridTuple) (u μ : Fin 8 → Fin 4 → ℂ)
    (H : Fin 8 → Fin 2 → ℂ) (U : Fin 4 → Fin 2 → ℂ) (A : Fin 8 → ℂ) (a : Fin 4 → ℂ) :
    LiftCoord → ℂ :=
  Sum.elim x (Sum.elim (fun ⟨⟨i,j⟩,h⟩ ↦ ![u i j,μ i j,(A i-a j)⁻¹] h)
    (fun ⟨s,h⟩ ↦ s.elim (fun i ↦ ![H i 0,H i 1,A i] h) (fun j ↦ ![U j 0,U j 1,a j] h)))

/-- Projection of the lifted polynomial zero set agrees exactly, point by
point, with the concrete twelve-position equations and the two curve tests. -/
theorem projected_grid_locus (f g : Poly₂) :
    (fun (y : LiftCoord → ℂ) i ↦ y (.inl i)) '' equations (List.ofFn edgeList ++ List.ofFn (curveList f g)) =
    {x | x ∈ curveProduct f g ∧ PositionSystem x} := by
  classical
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨hE,hC⟩ := (all_lift_eqs f g y).mp hy
    refine ⟨(curve_eval f g y).mp hC,fun i j ↦ y (.inr (.inl ((i,j),0))),
      fun i j ↦ y (.inr (.inl ((i,j),1))),fun i d ↦ y (.inr (.inr (.inl i,d.castSucc))),
      fun j d ↦ y (.inr (.inr (.inr j,d.castSucc))),fun i ↦ y (.inr (.inr (.inl i,2))),
      fun j ↦ y (.inr (.inr (.inr j,2))),?_⟩
    intro i j
    have h₀ := hE i j 0
    have h₁ := hE i j 1
    have h₂ := hE i j 2
    have h₃ := hE i j 3
    simp [edgeEquation,point,velocity,edgeVar,dv,dw,sub_eq_zero] at h₀ h₁ h₂ h₃
    refine ⟨h₀,h₁,sub_ne_zero.mp (right_ne_zero_of_mul_eq_one h₃),?_⟩
    have hc₀ : (0 : Fin 2).castSucc = (0 : Fin 3) := rfl
    have hc₁ : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
    convert h₂ using 1 <;> simp only [hc₀,hc₁,div_eq_mul_inv,mul_inv_rev,Complex.inv_I] <;> ring
  · rintro ⟨hX,u,μ,H,U,A,a,hs⟩
    let y := packed x u μ H U A a
    refine ⟨y,(all_lift_eqs f g y).mpr ⟨?_,(curve_eval f g y).mpr hX⟩,rfl⟩
    intro i j h
    obtain ⟨h₀,h₁,h₂,h₃⟩ := hs i j
    fin_cases h <;> simp [y,packed,edgeEquation,point,velocity,edgeVar,dv,dw,sub_eq_zero]
    · exact h₀
    · exact h₁
    · convert h₃ using 1 <;> simp only [div_eq_mul_inv,mul_inv_rev,Complex.inv_I] <;> ring
    · exact inv_mul_cancel₀ (sub_ne_zero.mpr h₂)


end PlanarUnitDistances.Competition.GridElimination
