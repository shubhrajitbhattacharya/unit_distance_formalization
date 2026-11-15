import PlanarUnitDistances.GridLocus
import PlanarUnitDistances.GridElimination

namespace PlanarUnitDistances.GridLocus
open MvPolynomial Finset
open scoped ComplexConjugate Classical
noncomputable section

private theorem vec_eta (p : Point) : ![p 0,p 1]=p := by funext i; fin_cases i <;> rfl
private theorem reflected_vec (z w : ℂ) : CurveReflection.reflectPoint ![z,w]=![conj w,conj z] := by
  funext i; fin_cases i <;> rfl

theorem pair_equiv (f g : PlanePoly) : curvePair f g ↔ Competition.CurvePair f g := by
  constructor
  · rintro ⟨a,b⟩
    refine ⟨?_,b⟩
    intro h hh
    obtain ⟨irr,refl,proj⟩ := a h (by simpa using hh)
    exact ⟨irr,fun z w => (refl ![z,w]).trans (by rw [reflected_vec]),proj⟩
  · rintro ⟨a,b⟩
    refine ⟨?_,b⟩
    intro h hh
    obtain ⟨irr,refl,proj⟩ := a h (by simpa using hh)
    refine ⟨irr,fun p => ?_,proj⟩
    have v := refl (p 0) (p 1)
    rw [← reflected_vec,vec_eta p] at v
    exact v

private theorem cart_differences (p r : Point) :
    cart p 0-cart r 0=((p 0-r 0)+(p 1-r 1))/2 ∧
    cart p 1-cart r 1=((p 0-r 0)-(p 1-r 1))/(2*Complex.I) := by
  constructor <;> simp [cart] <;> ring

theorem position_equiv (u : Tuple) :
    compatibleTuple u ↔ Competition.PositionSystem (fun e => u e.1 e.2) := by
  constructor
  · rintro ⟨d,H,U,A,a,h⟩
    refine ⟨d,fun i j => (d i j)⁻¹,H,U,A,a,?_⟩
    intro i j
    obtain ⟨hd,dist,ne,mot⟩ := h i j
    obtain ⟨x,y⟩ := cart_differences (u (.inl i)) (u (.inr j))
    exact ⟨mul_inv_cancel₀ hd,dist,ne,by rwa [x,y] at mot⟩
  · rintro ⟨d,v,H,U,A,a,h⟩
    refine ⟨d,H,U,A,a,?_⟩
    intro i j
    obtain ⟨hinv,dist,ne,mot⟩ := h i j
    have hn : d i j ≠ 0 := by rintro hz; simp [hz] at hinv
    have eq : v i j=(d i j)⁻¹ := by apply mul_left_cancel₀ hn; simpa [hn] using hinv
    obtain ⟨x,y⟩ := cart_differences (u (.inl i)) (u (.inr j))
    rw [eq] at dist mot
    exact ⟨hn,dist,ne,by rwa [x,y]⟩


end
end PlanarUnitDistances.GridLocus
