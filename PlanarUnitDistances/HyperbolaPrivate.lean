import PlanarUnitDistances.RationalPrivateZeros
import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace PlanarUnitDistances.RationalPrivateZeros
open Polynomial
open scoped Polynomial
noncomputable section

variable {k K : Type*} [Field k] [CharZero k] [Field K] [CharZero K] [Algebra k K]

private def num {R : Type*} [CommRing R] (b z a : R) := -b*(z-a)^2
private def den {R : Type*} [CommRing R] (u z a : R) := (z-u)*(a-u)

omit [CharZero k] [CharZero K] in
private theorem off_diag (u b t : k) (hb : b≠0) (a : Fin 4 → K)
    (ind : AlgebraicIndependent k a) {i j : Fin 4} (ne : j≠i) :
    let s := algebraMap k K u+algebraMap k K t*(a i-algebraMap k K u)
    let n := num (algebraMap k K b) s (a j)
    n*(n-4*den (algebraMap k K u) s (a j))≠0 := by
  let A : Fin 4 → MvPolynomial (Fin 4) k := MvPolynomial.X
  let U : MvPolynomial (Fin 4) k := MvPolynomial.C u
  let z := U+MvPolynomial.C t*(A i-U)
  let N := num (MvPolynomial.C b) z (A j)
  let p := N*(N-4*den U z (A j))
  dsimp only
  intro h
  have eq : p=0 := ind.eq_zero_of_aeval_eq_zero p (by
    simpa [p,N,z,A,U,num,den,map_ofNat] using h)
  let y (l : Fin 4) := if l=j then u+1 else u
  have val := congrArg (MvPolynomial.eval y) eq
  simp [p,N,z,U,A,y,ne.symm,num,den,hb,map_ofNat] at val

omit [CharZero K] in
private theorem generic_ne_const (u : k) (a : Fin 4 → K) (ind : AlgebraicIndependent k a)
    (i : Fin 4) : a i≠algebraMap k K u := by
  intro h
  have eq : MvPolynomial.X i-MvPolynomial.C u=0 :=
    ind.eq_zero_of_aeval_eq_zero _ (by simp [h])
  have bad := congrArg (MvPolynomial.eval fun _ => u+1) eq
  simp at bad

def hyperbolaNum (b a : K) : K[X] := num (C b) X (C a)
def hyperbolaDen (u a : K) : K[X] := den (C u) X (C a)

omit [CharZero K] in
/-- For the shifted hyperbola (z-u)(w-v)=b, the squared distance to the
anchor with abscissa a is -b*(z-a)^2/((z-u)*(a-u)). -/
theorem hyperbola_chord (b u v z a : K) (hz : z≠u) (ha : a≠u) :
    (z-a)*((v+b/(z-u))-(v+b/(a-u)))= -b*(z-a)^2/((z-u)*(a-u)) := by
  field_simp [sub_ne_zero.mpr hz, sub_ne_zero.mpr ha]
  ring

/-- Private orders for the four actual rational radicands, on the same
nonunit hyperbola. The simple root t must be chosen over the original
coefficient field; extending that field afterwards does not alter the
computed orders. -/
theorem hyperbola_private_orders_at_root (u b t : k) (hb : b≠0) (hb1 : b≠1)
    (root : b*t^2+(4-2*b)*t+b=0) (a : Fin 4 → K) (ind : AlgebraicIndependent k a) :
    ∃ D : Fin 4 → (RatFunc K)ˣ, FourRowObstruction.PrivateOrders D ∧ ∀ i,
      let l := algebraMap K[X] (RatFunc K) (hyperbolaNum (algebraMap k K b) (a i)) /
        algebraMap K[X] (RatFunc K) (hyperbolaDen (algebraMap k K u) (a i))
      (D i:RatFunc K)=l*(l-4) := by
  let U := algebraMap k K u
  let B := algebraMap k K b
  let T := algebraMap k K t
  have b0 : B≠0 := by simpa only [B,map_zero] using (algebraMap k K).injective.ne hb
  have b1 : B≠1 := by simpa only [B,map_one] using (algebraMap k K).injective.ne hb1
  have rt : B*T^2+(4-2*B)*T+B=0 := by
    simpa only [B,T,map_add,map_sub,map_ofNat,map_pow,map_zero,map_mul]
      using congrArg (algebraMap k K) root
  have t0 : T≠0 := by intro h; simp [h,b0] at rt
  have sep : -2*B*(T-1)-4≠0 := by
    intro h
    apply b1
    apply eq_of_sub_eq_zero
    linear_combination (B/4)*rt + ((2*B*T-2*B+4)/16)*h
  let N i := hyperbolaNum B (a i)
  let Q i := hyperbolaDen U (a i)
  let P i := N i*(N i-4*Q i)
  let s i := U+T*(a i-U)
  have a0 i : a i-U≠0 := sub_ne_zero.mpr (generic_ne_const u a ind i)
  have nzs i : s i-U≠0 := by simpa [s] using mul_ne_zero t0 (a0 i)
  have qval i j : (Q j).eval (s i)=(s i-U)*(a j-U) := by simp [Q,hyperbolaDen,den]
  have qne i j : (Q j).eval (s i)≠0 := qval i j ▸ mul_ne_zero (nzs i) (a0 j)
  have nval i j : (N j).eval (s i)= -B*(s i-a j)^2 := by simp [N,hyperbolaNum,num]
  have rn i : (N i).eval (s i)=4*(Q i).eval (s i) := by
    rw [nval,qval]
    dsimp [s]
    linear_combination -(a i-U)^2*rt
  have rootP i : (P i).eval (s i)=0 := by simp [P,rn]
  have der i : ((N i).derivative.eval (s i)-4*(Q i).derivative.eval (s i))=
        (-2*B*(T-1)-4)*(a i-U) := by
    simp [N,Q,hyperbolaDen,hyperbolaNum,den,num,derivative_mul,derivative_pow,s]; ring
  have simpleP i : (P i).derivative.eval (s i)≠0 := by
    have h := mul_ne_zero (show 4*(Q i).eval (s i)≠0 from mul_ne_zero (by norm_num) (qne i i))
      (mul_ne_zero sep (a0 i))
    simpa [P,derivative_mul,rn,der] using h
  have other i j (ne : j≠i) : (P j).eval (s i)≠0 := by
    simpa only [P,eval_mul,eval_sub,eval_ofNat,nval,qval,num,den,s,B,U,T] using off_diag u b t hb a ind ne
  have pne i : P i≠0 := by intro h; have := simpleP i; simp [h] at this
  have q0 i : Q i≠0 := by intro h; have := qne i i; simp [h] at this
  let F := algebraMap K[X] (RatFunc K)
  have fp i : F (P i)≠0 := by simpa only [F,map_zero] using (RatFunc.algebraMap_injective K).ne (pne i)
  have fq i : F (Q i)≠0 := by simpa only [F,map_zero] using (RatFunc.algebraMap_injective K).ne (q0 i)
  let D i := Units.mk0 (F (P i) / F (Q i^2)) (div_ne_zero (fp i) (by simp [fq]))
  refine ⟨D,private_orders_of_simple_zeros P (fun i => Q i^2) D (by intro i; rfl)
    s rootP simpleP other (fun i j => by simp [qne]),fun i => ?_⟩
  change F (N i*(N i-4*Q i))/F (Q i^2)=F (N i)/F (Q i)*(F (N i)/F (Q i)-4)
  rw [map_mul,map_sub,map_mul,map_ofNat,map_pow]
  field_simp [fq]

/-- The nonunit hyperbola case needs only b different from zero and one.
The private roots are chosen over the original algebraically closed field. -/
theorem hyperbola_private_orders [IsAlgClosed k] (u b : k) (hb : b≠0) (hb1 : b≠1)
    (a : Fin 4 → K) (ind : AlgebraicIndependent k a) :
    ∃ D : Fin 4 → (RatFunc K)ˣ, FourRowObstruction.PrivateOrders D ∧ ∀ i,
      let l := algebraMap K[X] (RatFunc K) (hyperbolaNum (algebraMap k K b) (a i)) /
        algebraMap K[X] (RatFunc K) (hyperbolaDen (algebraMap k K u) (a i))
      (D i:RatFunc K)=l*(l-4) := by
  obtain ⟨w,hw⟩ := IsAlgClosed.exists_pow_nat_eq (1-b) (by decide : 0<2)
  apply hyperbola_private_orders_at_root u b ((b-2+2*w)/b) hb hb1 _ a ind
  field_simp [hb]
  linear_combination 4*hw

end
end PlanarUnitDistances.RationalPrivateZeros
