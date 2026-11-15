import PlanarUnitDistances.HyperbolaPrivate
import Mathlib.FieldTheory.RatFunc.AsPolynomial

namespace PlanarUnitDistances.RationalPrivateZeros
open FourRowObstruction IntermediateField Polynomial
open scoped Polynomial IntermediateField
noncomputable section
variable {k K E : Type*} [Field k] [CharZero k] [Field K] [CharZero K] [Algebra k K]
variable [Field E] [Algebra K E]

/-- Transport orders only across an actual field isomorphism. No extension
of a valuation to an ambient field of unknown ramification is involved. -/
theorem transport_private {F L : Type*} [Field F] [Field L] (e : F ≃+* L)
    {D : Fin 4 → Fˣ} (orders : PrivateOrders D) :
    PrivateOrders (fun i => Units.map e.toMonoidHom (D i)) := by
  intro i
  obtain ⟨v,hi,hrest⟩ := orders i
  let ψ := Units.map e.symm.toMonoidHom
  have cancel (d : Fˣ) : ψ (Units.map e.toMonoidHom d)=d := by
    apply Units.ext; exact e.symm_apply_apply _
  exact ⟨v.comp ψ,by simpa only [MonoidHom.comp_apply,cancel] using hi,
    fun j ne => by simpa only [MonoidHom.comp_apply,cancel] using hrest j ne⟩

/-- The private orders are on the actual field K(x) of the surviving row.
The chord lengths are identified in the original extension field E. -/
theorem line_at_transcendental (e c : k) (ec : e*c^2=4)
    (a : Fin 4 → K) (ind : AlgebraicIndependent k a) (x : E) (tr : Transcendental K x) :
    ∃ D : Fin 4 → (K⟮x⟯)ˣ, PrivateOrders D ∧ ∀ i,
      let l := algebraMap K E (algebraMap k K e)*(x-algebraMap K E (a i))^2
      ((D i : K⟮x⟯) : E)=l*(l-4) := by
  obtain ⟨D,ord,eq⟩ := line_private_orders e c ec a ind
  let φ := RatFunc.algEquivOfTranscendental x tr
  refine ⟨fun i => Units.map φ.toRingEquiv.toMonoidHom (D i),transport_private φ.toRingEquiv ord,?_⟩
  intro i
  change ((φ (D i : RatFunc K) : K⟮x⟯) : E)=_
  rw [eq]
  have hc (v : K) : ((RatFunc.algEquivOfTranscendental x tr (RatFunc.C v) : K⟮x⟯) : E)=algebraMap K E v := congrArg (fun z : K⟮x⟯ => (z : E)) (φ.commutes v)
  simp [φ,lineChord,hc,map_ofNat]
  exact Or.inl rfl

theorem hyperbola_at_transcendental [IsAlgClosed k] (u b : k) (hb : b≠0) (hb1 : b≠1)
    (a : Fin 4 → K) (ind : AlgebraicIndependent k a) (x : E) (tr : Transcendental K x) :
    ∃ D : Fin 4 → (K⟮x⟯)ˣ, PrivateOrders D ∧ ∀ i,
      let U := algebraMap K E (algebraMap k K u)
      let B := algebraMap K E (algebraMap k K b)
      let l := -B*(x-algebraMap K E (a i))^2/((x-U)*(algebraMap K E (a i)-U))
      ((D i : K⟮x⟯) : E)=l*(l-4) := by
  obtain ⟨D,ord,eq⟩ := hyperbola_private_orders u b hb hb1 a ind
  let φ := RatFunc.algEquivOfTranscendental x tr
  refine ⟨fun i => Units.map φ.toRingEquiv.toMonoidHom (D i),transport_private φ.toRingEquiv ord,?_⟩
  intro i
  change ((φ (D i : RatFunc K) : K⟮x⟯) : E)=_
  rw [eq]
  have hc (v : K) : ((RatFunc.algEquivOfTranscendental x tr (RatFunc.C v) : K⟮x⟯) : E)=algebraMap K E v := congrArg (fun z : K⟮x⟯ => (z : E)) (φ.commutes v)
  have hn (B a : K) : hyperbolaNum B a = -C B*(X-C a)^2 := rfl
  have hd (U a : K) : hyperbolaDen U a = (X-C U)*C (a-U) := by simp [show hyperbolaDen U a = (X-C U)*(C a-C U) from rfl]
  simp [φ,hn,hd,hc,map_ofNat]
  exact Or.inl rfl

end
end PlanarUnitDistances.RationalPrivateZeros
