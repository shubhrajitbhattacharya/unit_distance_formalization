import PlanarUnitDistances.CommonCoordinates
import PlanarUnitDistances.IncidenceIdentification
import PlanarUnitDistances.PhysicalInterface

namespace PlanarUnitDistances.ResearchPhysical
open OAI.PlanarUnitDistances CommonFieldModel Finset
open scoped Classical
noncomputable section
variable {P Q : Finset Competition.Plane}

private def liftCoord (M : Model P Q) (c : ℂ) : M.field :=
  if h : c∈M.field then ⟨c,h⟩ else 0

private theorem coord_mem (M : Model P Q) {p : Competition.Plane} (hp : p∈P∪Q) :
    zCoord p∈M.field ∧ star (zCoord p)∈M.field := by
  have H (v : P ⊕ Q) := And.intro ((M.z_eq v) ▸ (M.z v).prop) ((M.w_eq v) ▸ (M.w v).prop)
  rcases mem_union.mp hp with h|h
  · exact H (.inl ⟨p,h⟩)
  · exact H (.inr ⟨p,h⟩)

private theorem real_coordinates (M : Model P Q) {p : Competition.Plane} (hp : p∈P∪Q)
    (i : Fin 2) : IsAlgebraic ℚ (p i) := by
  obtain ⟨z,w⟩ := coord_mem M hp
  have two : (2:ℂ)∈M.field := M.field.natCast_mem 2
  have h : (p i:ℂ)∈M.field := by
    fin_cases i
    · have eq : (zCoord p+star (zCoord p))/2=(p 0:ℂ) := by
        apply (div_eq_iff (by norm_num)).mpr
        apply Complex.ext <;> simp [zCoord] <;> ring
      exact eq ▸ M.field.div_mem (M.field.add_mem z w) two
    · have eq : (zCoord p-star (zCoord p))/(2*Complex.I)=(p 1:ℂ) := by
        apply (div_eq_iff (mul_ne_zero (by norm_num) Complex.I_ne_zero)).mpr
        apply Complex.ext <;> simp [zCoord] <;> ring
      exact eq ▸ M.field.div_mem (M.field.sub_mem z w) (M.field.mul_mem two M.i_mem)
  let φ := IsScalarTower.toAlgHom ℚ ℝ ℂ
  apply (isAlgebraic_algHom_iff φ φ.injective).mp
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (⟨(p i:ℂ),h⟩ : M.field)).algHom M.field.val

/-- The exact graph and the exact field from the original large-height
piece, including all unit edges on P by Q and the same two null coordinates. -/
def toPiece (M : Model P Q) : Competition.IncidencePiece M.field where
  P := P
  Q := Q
  E := (P×ˢQ).filter (fun e => dist e.1 e.2=1)
  membership := filter_subset _ _
  algebraic := fun _ hp => real_coordinates M hp
  unit := fun e h => (mem_filter.mp h).2
  embedding := M.field.val.toRingHom
  imaginaryUnit := ⟨Complex.I,M.i_mem⟩
  imaginaryUnit_spec := rfl
  Z := fun p => liftCoord M (zCoord p)
  W := fun p => liftCoord M (star (zCoord p))
  coordinates := by
    intro p hp
    obtain ⟨a,b⟩ := coord_mem M hp
    change (liftCoord M (zCoord p) : ℂ)=zCoord p ∧ (liftCoord M (star (zCoord p)) : ℂ)=star (zCoord p)
    simp only [liftCoord,dif_pos a,dif_pos b,and_self]

theorem full (M : Model P Q) : Competition.IncidencePiece.Research.Full (toPiece M) :=
  fun _ hp _ hq d => mem_filter.mpr ⟨mem_product.mpr ⟨hp,hq⟩,d⟩

theorem z_point (M : Model P Q) (p : P) : (toPiece M).Z p=M.z (.inl p) := by
  apply Subtype.ext
  exact ((toPiece M).coordinates _ (mem_union_left _ p.prop)).1.trans (M.z_eq (.inl p)).symm

theorem z_center (M : Model P Q) (q : Q) : (toPiece M).Z q=M.z (.inr q) := by
  apply Subtype.ext
  exact ((toPiece M).coordinates _ (mem_union_right _ q.prop)).1.trans (M.z_eq (.inr q)).symm

theorem ratio (M : Model P Q) (p r : P) (q : Q) :
    Competition.tripleRatio (toPiece M) (p,q,r)=
      (M.z (.inl p)-M.z (.inr q))/(M.z (.inl r)-M.z (.inr q)) := by
  unfold Competition.tripleRatio
  rw [z_point,z_center,z_point]

end
end PlanarUnitDistances.ResearchPhysical
