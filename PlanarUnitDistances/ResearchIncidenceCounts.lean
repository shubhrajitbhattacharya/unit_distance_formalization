import PlanarUnitDistances.IncidenceIdentification
import PlanarUnitDistances.WalkBudget

namespace PlanarUnitDistances.Competition.IncidencePiece.Research
open Finset OAI.PlanarUnitDistances.CircleIncidence OAI.PlanarUnitDistances.FiniteInformation
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

/-- Exact count on every subrectangle of a full unit-incidence graph. -/
theorem rectangle_count (M : IncidencePiece K) (h : Full M)
    (A B : Finset Plane) (hA : A ⊆ M.P) (hB : B ⊆ M.Q) :
    ((M.E ∩ (A×ˢB)).card:ℝ) = OAI.PlanarUnitDistances.CircleIncidence.incidences A B := by
  have eq : M.E ∩ (A×ˢB) = (A×ˢB).filter (fun e => dist e.1 e.2=1) := by
    ext e
    obtain ⟨p,q⟩ := e
    simp only [mem_inter,mem_product,mem_filter]
    constructor
    · exact fun hx => ⟨hx.2,M.unit (p,q) hx.1⟩
    · exact fun hx => ⟨h p (hA hx.1.1) q (hB hx.1.2) hx.2,hx.1⟩
  rw [eq]
  simp only [OAI.PlanarUnitDistances.CircleIncidence.incidences,degree_sum,
    natCast_card_filter,sum_product_right]

theorem joint_eq (M : IncidencePiece K) (h : Full M) (p r : M.P) :
    M.joint p r = wedge (unitCenterLaw M.P M.Q) (fun q : M.Q => unitNeighborLaw M.P q) (p,r) := by
  unfold joint wedge
  apply sum_congr rfl
  intro q _
  rw [atom M h]
  by_cases hp : dist p.val q.val=1
  · have pm : p ∈ unitNeighbors M.P q := mem_filter.mpr ⟨mem_univ _,hp⟩
    have de : degree M.P q ≠ 0 :=
      ((unitNeighbors_card M.P q) ▸ (Nat.cast_pos.mpr (card_pos.mpr ⟨p,pm⟩) :
        (0:ℝ)<(unitNeighbors M.P q).card)).ne'
    by_cases hr : dist r.val q.val=1
    · have rm : r ∈ unitNeighbors M.P q := mem_filter.mpr ⟨mem_univ _,hr⟩
      simp only [hp,hr,and_self,ite_true,unitNeighborLaw,pm,rm,unitCenterLaw]
      by_cases edgeZero : OAI.PlanarUnitDistances.CircleIncidence.incidences M.P M.Q=0
      · simp [edgeZero]
      · field_simp [de,edgeZero]
    · have rm : r ∉ unitNeighbors M.P q := fun m => hr (mem_filter.mp m).2
      simp [hp,hr,unitNeighborLaw,rm]
  · have pm : p ∉ unitNeighbors M.P q := fun m => hp (mem_filter.mp m).2
    simp [hp,unitNeighborLaw,pm]

/-- The mutual informations agree, including every diagonal atom and every
zero-mass term. This identity does not need positive minimum degree. -/
theorem information_eq (M : IncidencePiece K) (h : Full M) :
    M.information = unitWalkInformation M.P M.Q := by
  unfold information unitWalkInformation KL
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro r _
  simp only [unitWalk_marginal_eq_degree,point_marginal M h,joint_eq M h]

/-- Transport of all the numerical bounds once their original graph
form has been established. Both informations in the proof use the same law. -/
theorem regular_of_estimates (B : IncidencePiece K) (hfull : Full B) (t : ℝ)
    (hm : t^(1+2*savingA-173*savingG) ≤ B.P.card)
    (hM : (B.P.card:ℝ) ≤ 2*t^(1+2*savingA)) (hn : (B.Q.card:ℝ) ≤ t^(2+savingA))
    (he : t^(2+2*savingA-90*savingG) ≤ OAI.PlanarUnitDistances.CircleIncidence.incidences B.P B.Q)
    (hp : ∀ p∈B.P, (27/100:ℝ)*t^(1-90*savingG) ≤ degree B.Q p ∧ degree B.Q p ≤ t^(1+10*savingG) ∧
      (27/50:ℝ)/B.P.card ≤ degree B.Q p/OAI.PlanarUnitDistances.CircleIncidence.incidences B.P B.Q ∧
      degree B.Q p/OAI.PlanarUnitDistances.CircleIncidence.incidences B.P B.Q ≤ t^(-1-2*savingA+100*savingG))
    (hq : ∀ q∈B.Q, (27/50:ℝ)*t^(savingA-90*savingG) ≤ degree B.P q ∧ degree B.P q ≤ t^(savingA+10*savingG) ∧
      (27/50:ℝ)/B.Q.card ≤ degree B.P q/OAI.PlanarUnitDistances.CircleIncidence.incidences B.P B.Q)
    (hrect : ∀ A ⊆ B.P, ∀ C ⊆ B.Q, let v := (A.card:ℝ)/B.P.card*((C.card:ℝ)/B.Q.card)
      OAI.PlanarUnitDistances.CircleIncidence.incidences A C/OAI.PlanarUnitDistances.CircleIncidence.incidences B.P B.Q
        ≤ Real.sqrt v*(v^(1/25:ℝ)+t^(-150*savingG)))
    (hI : unitWalkInformation B.P B.Q+1 ≤ 10200*savingG*Real.log t) : Regular B t := by
  have edges : (B.E.card:ℝ) = OAI.PlanarUnitDistances.CircleIncidence.incidences B.P B.Q := edge_count B hfull
  have pd (p : Competition.Plane) (hp : p∈B.P) : (B.degreeP p:ℝ)=degree B.Q p := point_degree B hfull p hp
  have qd (q : Competition.Plane) (hq : q∈B.Q) : (B.degreeQ q:ℝ)=degree B.P q := center_degree B hfull q hq
  have pm (p : Competition.Plane) (hp : p∈B.P) : B.mu p=degree B.Q p/OAI.PlanarUnitDistances.CircleIncidence.incidences B.P B.Q :=
    point_marginal B hfull ⟨p,hp⟩
  have qm (q : Competition.Plane) (hq : q∈B.Q) : B.kappa q=degree B.P q/OAI.PlanarUnitDistances.CircleIncidence.incidences B.P B.Q :=
    center_marginal B hfull ⟨q,hq⟩
  change Competition.Regular B t
  refine ⟨hm,hM,hn,edges.symm ▸ he,?_,?_,?_,?_,?_,?_⟩
  · intro p pp
    rw [pd p pp]
    exact ⟨(by simpa only [Competition.gamma,show (27/50:ℝ)/2=27/100 by norm_num]
              using (hp p pp).1),(hp p pp).2.1⟩
  · intro q qq
    rw [qd q qq]
    exact ⟨(hq q qq).1,(hq q qq).2.1⟩
  · intro p pp
    rw [pm p pp]
    exact (hp p pp).2.2
  · intro q qq
    rw [qm q qq]
    exact (hq q qq).2.2
  · intro A C ha hc
    dsimp only
    rw [rectangle_count B hfull A C ha hc,edges]
    exact hrect A ha C hc
  · rw [information_eq B hfull]
    exact hI

end
end PlanarUnitDistances.Competition.IncidencePiece.Research

