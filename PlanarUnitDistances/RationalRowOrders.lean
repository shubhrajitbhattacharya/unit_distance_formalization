import PlanarUnitDistances.RationalCurveCase
import PlanarUnitDistances.RowPrivateField

namespace PlanarUnitDistances.RationalCurveCase
open MvPolynomial Competition Set IntermediateField RationalPrivateZeros FourRowObstruction
open scoped IntermediateField
noncomputable section
variable {K E : Type} [Field K] [CharZero K] [Algebra ℂ K] [Field E]
  [Algebra K E] [Algebra ℂ E] [IsScalarTower ℂ K E]

private theorem eval_of_dvd {T : Type} [Field T] [Algebra ℂ T] {f h : Poly₂}
    (dvd : f∣h) (x : Fin 2 → T) (on : aeval x f=0) : aeval x h=0 := by
  obtain ⟨q,rfl⟩ := dvd
  simp [on]

private theorem line_value {T : Type} [Field T] [Algebra ℂ T] {e c : ℂ} {x w : T}
    (on : aeval ![x,w] (lineEq e c)=0) :
    w=algebraMap ℂ T e*x+algebraMap ℂ T c := by
  simpa [lineEq,sub_eq_zero] using on

private theorem hyper_value {T : Type} [Field T] [Algebra ℂ T] {u v b : ℂ} (ne : b≠0) {x w : T}
    (on : aeval ![x,w] (hyperEq u v b)=0) :
    x≠algebraMap ℂ T u ∧ w=algebraMap ℂ T v+algebraMap ℂ T b/(x-algebraMap ℂ T u) := by
  have eq : (x-algebraMap ℂ T u)*(w-algebraMap ℂ T v)=algebraMap ℂ T b := by
    simpa [hyperEq,sub_eq_zero] using on
  have nz : x-algebraMap ℂ T u≠0 := by
    intro h
    have := (algebraMap ℂ T).injective.ne ne
    exact this (by simpa [h] using eq.symm)
  refine ⟨sub_ne_zero.mp nz,?_⟩
  have := (eq_div_iff nz).mpr ((mul_comm _ _).trans eq)
  linear_combination this

theorem orders_on_rational_row {f g : Poly₂} (pair : CurvePair f g)
    (same : g∣f) (one : f.degreeOf 1=1) (x w : E) (tr : Transcendental K x)
    (on : aeval ![x,w] f=0) (a b : Fin 4 → K) (ind : AlgebraicIndependent ℂ a)
    (anchors : ∀ j,aeval ![a j,b j] g=0) :
    ∃ M : IntermediateField K E,x∈M ∧ w∈M ∧ ∃ D : Fin 4 → Mˣ,
      PrivateOrders D ∧ ∀ j,let l := (x-algebraMap K E (a j))*(w-algebraMap K E (b j))
                            (((D j : M) : E))=l*(l-4) := by
  let M := K⟮x⟯
  have xmem : x∈M := IntermediateField.mem_adjoin_simple_self _ _
  have mapc (c : ℂ) : algebraMap ℂ E c=algebraMap K E (algebraMap ℂ K c) :=
    IsScalarTower.algebraMap_apply ℂ K E c
  have cmem (c : ℂ) : algebraMap ℂ E c ∈ M := mapc c ▸ M.algebraMap_mem _
  rcases classify pair same one with ⟨e,c,ne,hf,hg⟩|⟨u,v,β,nz,n1,hf,hg⟩
  · have hr := line_value (eval_of_dvd hf _ on)
    have ha (j) := line_value (eval_of_dvd hg _ (anchors j))
    obtain ⟨t,ht⟩ := IsAlgClosed.exists_pow_nat_eq (4/e) (by decide : 0<2)
    obtain ⟨D,orders,hD⟩ := line_at_transcendental e t (by rw [ht]; field_simp) a ind x tr
    refine ⟨M,xmem,hr ▸ M.add_mem (M.mul_mem (cmem e) xmem) (cmem c),D,orders,fun j => ?_⟩
    have len : (x-algebraMap K E (a j))*(w-algebraMap K E (b j)) =
        algebraMap K E (algebraMap ℂ K e)*(x-algebraMap K E (a j))^2 := by
      rw [hr,ha,map_add,map_mul,mapc,mapc]; ring
    dsimp only
    rw [len]; exact hD j
  · obtain ⟨nx,hr⟩ := hyper_value nz (eval_of_dvd hf _ on)
    have ha (j) := hyper_value nz (eval_of_dvd hg _ (anchors j))
    obtain ⟨D,orders,hD⟩ := hyperbola_at_transcendental u β nz n1 a ind x tr
    refine ⟨M,xmem,hr ▸ M.add_mem (cmem v) (M.div_mem (cmem β) (M.sub_mem xmem (cmem u))),
      D,orders,fun j => ?_⟩
    have na := (algebraMap K E).injective.ne (ha j).1
    have h := hyperbola_chord (algebraMap ℂ E β) (algebraMap ℂ E u) (algebraMap ℂ E v)
      x (algebraMap K E (a j)) nx (by rwa [mapc])
    have len : (x-algebraMap K E (a j))*(w-algebraMap K E (b j)) =
        -(algebraMap K E (algebraMap ℂ K β))*(x-algebraMap K E (a j))^2 /
          ((x-algebraMap K E (algebraMap ℂ K u))*(algebraMap K E (a j)-algebraMap K E (algebraMap ℂ K u))) := by
      rw [hr,(ha j).2,map_add,map_div₀,map_sub]
      simpa only [mapc] using h
    dsimp only
    rw [len]; exact hD j

end
end PlanarUnitDistances.RationalCurveCase
