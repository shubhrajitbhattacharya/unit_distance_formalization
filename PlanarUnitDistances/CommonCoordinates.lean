import PlanarUnitDistances.GeometricCodegree
import Mathlib

/- Adapted from OpenAI math UnitDistances/Sequence.lean, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, Apache-2.0. The common field includes i. -/
namespace OAI
namespace PlanarUnitDistances.CommonField
open Polynomial

theorem exists_normal_field (S : Finset ℂ) (halg : ∀ z∈S, IsAlgebraic ℚ z) :
    ∃ F : IntermediateField ℚ ℂ, (∀ z∈S,z∈F) ∧ FiniteDimensional ℚ F ∧ Normal ℚ F := by
  classical
  let A := IntermediateField.adjoin ℚ (S : Set ℂ)
  let : FiniteDimensional ℚ A := IntermediateField.finiteDimensional_adjoin
    (fun z hz => (halg z hz).isIntegral)
  let F := IntermediateField.normalClosure ℚ A ℂ
  let : IsNormalClosure ℚ A F := Algebra.IsAlgebraic.isNormalClosure_normalClosure
    (fun _ => IsAlgClosed.splits _)
  let : Normal ℚ F := IsNormalClosure.normal (F := ℚ) (K := A) (L := F)
  refine ⟨F,?_,inferInstance,inferInstance⟩
  intro z hz
  exact (A.val.fieldRange_le_normalClosure (K := A))
    ⟨⟨z,IntermediateField.subset_adjoin ℚ _ hz⟩,rfl⟩

lemma integral_I : IsIntegral ℚ Complex.I := by
  refine ⟨X^2+1,?_,?_⟩
  · exact monic_X_pow_add_C 1 (by decide : 2 ≠ 0)
  · simp

lemma algebraic_ofReal {x : ℝ} (hx : IsAlgebraic ℚ x) : IsAlgebraic ℚ (x : ℂ) :=
  (hx.isIntegral.map (IsScalarTower.toAlgHom ℚ ℝ ℂ)).isAlgebraic

lemma algebraic_coordinates (x : EuclideanSpace ℝ (Fin 2))
    (hx : ∀ i,IsAlgebraic ℚ (x i)) :
    IsAlgebraic ℚ ((x 0 : ℂ)+(x 1 : ℂ)*Complex.I) ∧
    IsAlgebraic ℚ ((x 0 : ℂ)-(x 1 : ℂ)*Complex.I) := by
  have h0 := (algebraic_ofReal (hx 0)).isIntegral
  have h1 := (algebraic_ofReal (hx 1)).isIntegral
  exact ⟨(h0.add (h1.mul integral_I)).isAlgebraic,(h0.sub (h1.mul integral_I)).isAlgebraic⟩
end PlanarUnitDistances.CommonField

namespace PlanarUnitDistances.CommonFieldModel
open scoped Classical
noncomputable section
abbrev Plane := EuclideanSpace ℝ (Fin 2)
variable (P Q : Finset Plane)
def location : P ⊕ Q → Plane := Sum.elim Subtype.val Subtype.val

structure Model where
  field : IntermediateField ℚ ℂ
  finite : FiniteDimensional ℚ field
  normal : Normal ℚ field
  i_mem : Complex.I ∈ field
  z : P ⊕ Q → field
  w : P ⊕ Q → field
  z_eq : ∀v,(z v:ℂ)=_root_.PlanarUnitDistances.zCoord (location P Q v)
  w_eq : ∀v,(w v:ℂ)=star (_root_.PlanarUnitDistances.zCoord (location P Q v))

variable {P Q}
instance (M : Model P Q) : FiniteDimensional ℚ M.field := M.finite
instance (M : Model P Q) : Normal ℚ M.field := M.normal
instance (M : Model P Q) : NumberField M.field := ⟨⟩

theorem exists_model
    (hP : ∀p∈P,∀i,IsAlgebraic ℚ (p i))
    (hQ : ∀q∈Q,∀i,IsAlgebraic ℚ (q i)) : Nonempty (Model P Q) := by
  let Z := fun v : P⊕Q => _root_.PlanarUnitDistances.zCoord (location P Q v)
  let W := fun v : P⊕Q => star (Z v)
  have ha (v : P⊕Q) : IsAlgebraic ℚ (Z v) ∧ IsAlgebraic ℚ (W v) := by
    have h : ∀i,IsAlgebraic ℚ (location P Q v i) := by
      cases v with
      | inl p => exact hP p p.property
      | inr q => exact hQ q q.property
    have hh := CommonField.algebraic_coordinates (location P Q v) h
    have hz (x : Plane) : _root_.PlanarUnitDistances.zCoord x = (x 0 : ℂ)+(x 1 : ℂ)*Complex.I := by
      exact Complex.mk_eq_add_mul_I _ _
    simpa [Z,W,hz,sub_eq_add_neg] using hh
  let S : Finset ℂ := insert Complex.I (Finset.univ.image Z ∪ Finset.univ.image W)
  have halg : ∀z∈S,IsAlgebraic ℚ z := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact CommonField.integral_I.isAlgebraic
    rcases Finset.mem_union.mp hz with hz|hz
    · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hz
      exact (ha v).1
    · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hz
      exact (ha v).2
  obtain ⟨F,hF,hfin,hnorm⟩ := CommonField.exists_normal_field S halg
  refine ⟨⟨F,hfin,hnorm,hF _ (Finset.mem_insert_self ..),fun v => ⟨Z v,hF _ ?_⟩,fun v => ⟨W v,hF _ ?_⟩,
    fun _ => rfl,fun _ => rfl⟩⟩
  · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩))
  · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩))

namespace Model
variable (M : Model P Q)
lemma point_injective : Function.Injective (M.z ∘ Sum.inl) := by
  intro p r h
  apply Subtype.val_injective
  apply _root_.PlanarUnitDistances.zCoord_injective
  have hh := congrArg (fun x : M.field => (x:ℂ)) h
  simpa only [Function.comp_apply,M.z_eq,location,Sum.elim_inl] using hh
lemma center_injective : Function.Injective (M.z ∘ Sum.inr) := by
  intro q r h
  apply Subtype.val_injective
  apply _root_.PlanarUnitDistances.zCoord_injective
  have hh := congrArg (fun x : M.field => (x:ℂ)) h
  simpa only [Function.comp_apply,M.z_eq,location,Sum.elim_inr] using hh
lemma unit_identity (p : P) (q : Q) (h : dist (p:Plane) (q:Plane)=1) :
    (M.z (.inl p)-M.z (.inr q))*(M.w (.inl p)-M.w (.inr q))=1 := by
  apply Subtype.val_injective
  change ((M.z (.inl p):ℂ)-(M.z (.inr q):ℂ))*((M.w (.inl p):ℂ)-(M.w (.inr q):ℂ))=1
  simp only [M.z_eq,M.w_eq,location,Sum.elim_inl,Sum.elim_inr]
  exact _root_.PlanarUnitDistances.unit_edge_reciprocal h

lemma wpoint_injective : Function.Injective (M.w ∘ Sum.inl) := by
  intro p r h
  apply M.point_injective
  apply Subtype.val_injective
  have hh := congrArg (fun x : M.field => (x:ℂ)) h
  simp only [Function.comp_apply,M.w_eq,location,Sum.elim_inl] at hh
  simpa only [Function.comp_apply,M.z_eq,location,Sum.elim_inl] using star_injective hh

end Model
end
end PlanarUnitDistances.CommonFieldModel
end OAI
