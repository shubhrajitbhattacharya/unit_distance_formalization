import PlanarUnitDistances.ResearchRecordAgreement

namespace PlanarUnitDistances.ResearchPhysical
open OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence CommonFieldModel
open Competition.IncidencePiece PhysicalLevels CommonTemplate CrossStructure FiniteLaw RareScore
open Finset FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q : Finset Competition.Plane} {M : Model P Q}
variable {b : CoordinateLevel (toPiece M).Label} {t : Record P Q}

private theorem eps_dy : Competition.eps=ComparisonConstants.dy 1800 := by
  unfold Competition.eps ComparisonConstants.dy
  rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2)]; norm_cast

theorem RecordAgreement.good_iff (H : RecordAgreement M b t) (he : 0 < incidences P Q) :
    (toPiece M).goodRare b ↔ t∈PhysicalLevels.goodRare (incidenceLaw P Q he) := by
  obtain ⟨f,m⟩ := H.rare_masses he
  change _ ↔ ¬(_≤_) ∧ _≤_
  simp only [Competition.IncidencePiece.goodRare,f,m,eps_dy,not_le]

private theorem exceptional_shared {A : Type*} (r : Bool) (c x : A×A) :
    exceptional r c x ↔ shared r x≠shared r c := by cases r <;> rfl

theorem RecordAgreement.selected_points (H : RecordAgreement M b t) (he : 0 < incidences P Q) (p r : P) :
    b.selected p.val=b.selected r.val ↔
      shared (rareBit (incidenceLaw P Q he) t) (t.x p)=shared (rareBit (incidenceLaw P Q he) t) (t.x r) := by
  obtain ⟨z,w⟩ := H.classes (.inl p) (.inl r)
  cases k : rareBit (incidenceLaw P Q he) t
  · simpa [CoordinateLevel.selected,H.rare_bit he,k,shared,tagState,planeVertex] using z
  · simpa [CoordinateLevel.selected,H.rare_bit he,k,shared,tagState,planeVertex] using w

/-- The original tagged dominant label and the arithmetic label select
exactly the same point class on a good rare record. Each only has to
satisfy its own marginal exception bound. -/
theorem RecordAgreement.exception_iff (H : RecordAgreement M b t) (he : 0 < incidences P Q)
    (a : (toPiece M).Label) (c : Finset (P⊕Q)×Finset (P⊕Q))
    (good : (toPiece M).goodRare b) (da : (toPiece M).dominantAt b a)
    (dc : pointException (incidenceLaw P Q he) (rareBit (incidenceLaw P Q he) t) c t.x+
        centerException (incidenceLaw P Q he) (rareBit (incidenceLaw P Q he) t) c t.y ≤
      2*(minority (incidenceLaw P Q he) t+inconsistency (incidenceLaw P Q he) t.bit t.x t.y)) :
    ∀p : P,b.selected p.val≠a ↔ exceptional (rareBit (incidenceLaw P Q he) t) c (t.x p) := by
  let G := toPiece M
  let π := incidenceLaw P Q he
  let k := rareBit π t
  let A (e : P×Q) := b.selected e.1.val≠a
  let B (e : P×Q) := exceptional k c (t.x e.1)
  have point : event π A=G.pointMass (fun p => b.selected p≠a) := by
    rw [←G.edgeProb_point_event]
    exact (physical_event M he _ _ (fun _ _ _ => Iff.rfl)).symm
  have commonPoint : ∃p : P,b.selected p.val=a ∧ ¬exceptional k c (t.x p) := by
    by_contra hn
    have cover := event_mono π (P:=fun _ => True) (Q:=fun e => A e ∨ B e) (fun e _ => by
      by_cases h : b.selected e.1.val=a
      · right; by_contra hc; exact hn ⟨e.1,h,hc⟩
      · exact Or.inl h)
    rw [event_true] at cover
    have bound := cover.trans (event_union_le π A B)
    rw [point] at bound
    change 1≤G.pointMass _+pointException π k c t.x at bound
    have n₁ : 0≤G.centerMass (fun q => b.selected q≠a) := by
      unfold Competition.IncidencePiece.centerMass Competition.IncidencePiece.kappa; positivity
    have n₂ : 0≤centerException π k c t.y := event_nonneg .. 
    have f := (H.rare_masses he).1
    have m := (H.rare_masses he).2
    change G.minorityMass b=minority π t at f
    change G.inconsistentMass b=inconsistency π t.bit t.x t.y at m
    change _+centerException π k c t.y ≤ 2*(minority π t+inconsistency π t.bit t.x t.y) at dc
    rw [←f,←m] at dc
    change G.pointMass _+G.centerMass _ ≤ 2*(G.minorityMass b+G.inconsistentMass b) at da
    have ep : Competition.eps≤(2:ℝ)^(-3:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num : -(1800:ℝ)≤ -3)
    norm_num at ep
    linarith only [bound,n₁,n₂,da,dc,good.1,good.2,ep]
  obtain ⟨r,ar,cr⟩ := commonPoint
  have cr' : shared k (t.x r)=shared k c := Classical.not_not.mp ((not_congr (exceptional_shared k c (t.x r))).mp cr)
  intro p
  have eq := H.selected_points he p r
  change b.selected p.val=b.selected r.val ↔ shared k (t.x p)=shared k (t.x r) at eq
  rw [ar,cr'] at eq
  exact (not_congr eq).trans (exceptional_shared k c (t.x p)).symm


end
end PlanarUnitDistances.ResearchPhysical
