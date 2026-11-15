import PlanarUnitDistances.SmoothCurveOrders

/-! Obstruction on a smooth private sheet using the original reciprocal
labels. The null-coordinate tangent equations are linear in the two row
velocities and the row scalar. No ambient derivation is required. -/

noncomputable section

namespace PlanarUnitDistances.SmoothCurveOrders
open FourRowObstruction Polynomial OAI.PlanarUnitDistances
open BivariateMaps

private theorem independent_list {K : Type*} [Field K] (D : Fin 4 → Kˣ) (ord : PrivateOrders D) :
    Radicals.SquareIndependent [(D 0:K),(D 1:K),(D 2:K),(D 3:K)] := by
  classical
  let idx := List.ofFn (id : Fin 4 → Fin 4)
  let d (i : Fin 4) : K := D i
  have ind : Radicals.SquareIndependent (idx.map d) := by
    intro s hs hn c hc
    obtain ⟨js,seg,rfl⟩ := List.sublist_map_iff.mp hs
    have nd : js.Nodup := (List.nodup_ofFn.mpr Function.injective_id).sublist seg
    have hs' : js.toFinset.Nonempty := by
      cases js with
      | nil => exact (hn rfl).elim
      | cons a t => exact ⟨a,by simp⟩
    let q := js.toFinset.prod D
    have e : (q:K)=c^2 := by
      change (Units.coeHom K) (js.toFinset.prod D)=_
      rw [map_prod,List.prod_toFinset _ nd]
      exact hc
    have hcn : c≠0 := by
      rintro rfl
      exact q.ne_zero (by simpa using e)
    apply independent_of_private_orders ord _ hs' (Units.mk0 c hcn)
    exact Units.ext e
  simpa [idx,d,List.ofFn_succ,Fin.succ] using ind

universe u
variable {K L : Type u} [Field K] [Field L] [CharZero L] [Algebra K L]

/-- Private orders on the embedded generic function field are sufficient for
the original row equations in `L`, with their actual signed roots `m-u`. -/
theorem excludes_null_tangent (z w : L) (a b : Fin 4 → K)
    (orders : ∃ M : IntermediateField K L, z ∈ M ∧ w ∈ M ∧ ∃ D : Fin 4 → Mˣ,
      PrivateOrders D ∧ ∀ i, let l := (z-algebraMap K L (a i))*(w-algebraMap K L (b i))
                            (((D i : M) : L))=l*(l-4))
    (u m : Fin 4 → L) (inv : ∀ i, u i*m i=1)
    (chord : ∀ i,(z-algebraMap K L (a i))*(w-algebraMap K L (b i))=2-u i-m i)
    (U V t : Fin 4 → K) (H J A : L) (hne : ∀ i,A≠algebraMap K L (t i))
    (equations : ∀ i,(w-algebraMap K L (b i))*(H-algebraMap K L (U i))+
      (z-algebraMap K L (a i))*(J-algebraMap K L (V i))=(m i-u i)*(A-algebraMap K L (t i))) : False := by
  obtain ⟨M,hz,hw,D,ord,hD⟩ := orders
  let v (i : Fin 4) : M := (⟨w,hw⟩:M)-algebraMap K M (b i)
  let x (i : Fin 4) : M := (⟨z,hz⟩:M)-algebraMap K M (a i)
  have hv (i : Fin 4) : M.val (v i)=w-algebraMap K L (b i) := rfl
  have hx (i : Fin 4) : M.val (x i)=z-algebraMap K L (a i) := rfl
  have hr i : (m i-u i)^2=M.val (D i:M) := by
    rw [show M.val (D i:M)=_ from hD i]
    exact chord_root (inv i) (chord i)
  have hvzero : v 0≠0 := by
    intro zero
    have e := hv 0
    rw [zero,map_zero] at e
    have q := hD 0
    dsimp only at q
    rw [← e,mul_zero,zero_mul] at q
    exact (D 0).ne_zero (Subtype.ext q)
  apply Radicals.radical_system_impossible M.val.toRingHom (fun i ↦ (D i:M)) v x
    (fun i ↦ v i*algebraMap K M (U i)+x i*algebraMap K M (V i)) (algebraMap K M ∘ t)
    (independent_list D ord) (fun i ↦ m i-u i) hr hvzero H J A ?_ hne
  intro i
  change M.val (v i)*H+M.val (x i)*J-(m i-u i)*A=
    M.val (v i*algebraMap K M (U i)+x i*algebraMap K M (V i))-(m i-u i)*algebraMap K L (t i)
  rw [map_add,map_mul,map_mul,hv,hx]
  change (w-algebraMap K L (b i))*H+(z-algebraMap K L (a i))*J-(m i-u i)*A=
    (w-algebraMap K L (b i))*algebraMap K L (U i)+(z-algebraMap K L (a i))*algebraMap K L (V i)-
      (m i-u i)*algebraMap K L (t i)
  linear_combination equations i

end PlanarUnitDistances.SmoothCurveOrders
