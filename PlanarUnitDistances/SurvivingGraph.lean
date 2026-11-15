import PlanarUnitDistances.CommonCoordinates
import PlanarUnitDistances.GeometricHeightLaw
import PlanarUnitDistances.GoodPairs
import PlanarUnitDistances.LogHeight
import PlanarUnitDistances.Main

namespace PlanarUnitDistances
open OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open scoped Classical
noncomputable section

variable {P Q : Finset Plane}

def centerRatio (M : CommonFieldModel.Model P Q) (p r : P) (q : Q) : M.field :=
  (M.z (.inl p)-M.z (.inr q))/(M.z (.inl r)-M.z (.inr q))

theorem centerRatio_spec (M : CommonFieldModel.Model P Q) {p r : P} {q : Q}
    (hp : p ∈ unitRows P Q q) (hr : r ∈ unitRows P Q q) :
    centerRatio M p r q ≠ 0 ∧
    ((dist (p:Plane) (r:Plane)^2:ℝ):ℂ)=2-(centerRatio M p r q:ℂ)-(centerRatio M p r q:ℂ)⁻¹ := by
  have hp' : dist (p:Plane) (q:Plane)=1 := (Finset.mem_filter.mp hp).2
  have hr' : dist (r:Plane) (q:Plane)=1 := (Finset.mem_filter.mp hr).2
  have nz (i : P) (hi : dist (i:Plane) (q:Plane)=1) : M.z (.inl i)-M.z (.inr q) ≠ 0 := by
    intro h
    simpa [h] using M.unit_identity i q hi
  refine ⟨div_ne_zero (nz p hp') (nz r hr'),?_⟩
  simpa [centerRatio,M.z_eq,CommonFieldModel.location] using
    (planar_chord_identities hp' hr').1

/-- From the surviving triples with one endpoint potential per point to the
literal graph required by the manuscript. The same selected center defines the
ratio in both the individual and every rectangle height bound. -/
theorem graph_of_surviving_triples (hP : AlgebraicPoints P)
    (M : CommonFieldModel.Model P Q) (centers : P × P → Finset Q)
    (V : P → HeightPlace M.field → ℝ) (hV : ∀ p, FiniteAtPrimes (V p))
    (J d ε : ℝ) (hJ : 12*2^111 ≤ J) (hd : 0<d)
    (hdq : ∀ q, d ≤ ((unitRows P Q q).card : ℝ)) (he : 0 < incidences P Q)
    (mass : ε/16000 ≤ goodTripleMass (unitRows P Q) centers (incidences P Q))
    (survive : ∀ z q, q ∈ centers z →
      z.1 ≠ z.2 ∧ z.1 ∈ unitRows P Q q ∧ z.2 ∈ unitRows P Q q ∧
      J/3 ≤ weilHeight (centerRatio M z.1 z.2 q) ∧
      placeNorm (localLog (centerRatio M z.1 z.2 q) - (V z.2-V z.1)) ≤ J/(648*2^111) ∧
      ∀ c : Plane, dist (z.1:Plane) c = 1 → dist (z.2:Plane) c = 1 →
        (((P.filter fun x => dist x c = 1).card:ℕ):ℝ) < (P.card:ℝ)^(9/10:ℝ)) :
    ∃ G : AdmissibleGraph P.card M.field, G.points=P ∧ G.scale=J ∧
      ε*incidences P Q*d/32000 ≤ (G.edges.card:ℝ) := by
  classical
  let E := goodOrderedPairs centers
  obtain ⟨hc,w,hw⟩ := good_ordered_pairs_and_witnesses (@Subtype.val _ (· ∈ P))
    (@Subtype.val _ (· ∈ Q)) Subtype.val_injective Subtype.val_injective (unitRows P Q)
    (fun _ _ h => (Finset.mem_filter.mp h).2) centers
    (fun z q h => ⟨(survive z q h).1,(survive z q h).2.1,(survive z q h).2.2.1⟩)
    hd hdq _ he (unitRows_total P Q) mass
  let emb : (P × P) ↪ (Plane × Plane) := (Function.Embedding.subtype _).prodMap (Function.Embedding.subtype _)
  let Gedges := E.map emb
  have unpack {p r : Plane} (h : (p,r) ∈ Gedges) :
      ∃ (hp : p ∈ P) (hr : r ∈ P), (⟨p,hp⟩,⟨r,hr⟩)∈E := by
    obtain ⟨⟨i,j⟩,hm,eq⟩ := Finset.mem_map.mp h
    change ((i:Plane),(j:Plane)) = (p,r) at eq
    cases eq
    exact ⟨i.prop,j.prop,hm⟩
  let label (p r : Plane) : M.field :=
    if hp : p ∈ P then if hr : r ∈ P then
      if h : (⟨p,hp⟩,⟨r,hr⟩) ∈ E then centerRatio M ⟨p,hp⟩ ⟨r,hr⟩ (w ⟨_,h⟩)
      else 1 else 1 else 1
  have spec {p r : Plane} (h : (p,r) ∈ Gedges) :
      ∃ (i j : P), ↑i=p ∧ ↑j=r ∧ label p r ≠ 0 ∧
        ((dist p r^2:ℝ):ℂ)=2-(label p r:ℂ)-(label p r:ℂ)⁻¹ ∧
        J/3 ≤ weilHeight (label p r) ∧
        placeNorm (localLog (label p r) - (V j-V i)) ≤ J/(648*2^111) ∧
        ∀ c : Plane, dist p c = 1 → dist r c = 1 →
          (((P.filter fun x => dist x c = 1).card:ℕ):ℝ) < (P.card:ℝ)^(9/10:ℝ) := by
    obtain ⟨hp,hr,hE⟩ := unpack h
    let z : E := ⟨(⟨p,hp⟩,⟨r,hr⟩),hE⟩
    have good := survive z.val (w z) (hw z)
    have rat := centerRatio_spec M good.2.1 good.2.2.1
    refine ⟨z.val.1,z.val.2,rfl,rfl,?_⟩
    simpa only [label,dif_pos hp,dif_pos hr,dif_pos hE,z] using
      And.intro rat.1 (And.intro rat.2 good.2.2.2)
  refine ⟨{
    embedding := M.field.subtype
    points := P
    algebraic := hP
    point_bound := le_rfl
    edges := Gedges
    endpoints := ?_
    label := label
    scale := J
    scale_bound := hJ
    nonzero := ?_
    chord := ?_
    large_height := ?_
    rectangle := ?_
    circle := ?_ },rfl,rfl,?_⟩
  · rintro ⟨p,r⟩ h
    obtain ⟨hp,hr,_⟩ := unpack h
    exact ⟨hp,hr⟩
  · intro p r h
    obtain ⟨_,_,_,_,h',_⟩ := spec h
    exact h'
  · intro p r h
    obtain ⟨_,_,_,_,_,h',_⟩ := spec h
    exact h'
  · intro p r h
    obtain ⟨_,_,_,_,_,_,h',_⟩ := spec h
    exact h'
  · intro p p' r r' h11 h22 h12 h21
    obtain ⟨i,j,rfl,rfl,n11,_,_,b11,_⟩ := spec h11
    obtain ⟨k,l,rfl,rfl,n22,_,_,b22,_⟩ := spec h22
    obtain ⟨i',l',hi,hl,n12,_,_,b12,_⟩ := spec h12
    obtain ⟨k',j',hk,hj,n21,_,_,b21,_⟩ := spec h21
    obtain rfl := Subtype.val_injective hi
    obtain rfl := Subtype.val_injective hl
    obtain rfl := Subtype.val_injective hk
    obtain rfl := Subtype.val_injective hj
    have hh := quotient_height_of_endpoint_errors n11 n12 n21 n22 _ _ _ _
      (hV i') (hV k') (hV j') (hV l') _ b11 b12 b21 b22
    convert hh using 1
    ring
  · intro p r h
    obtain ⟨_,_,_,_,_,_,_,_,h'⟩ := spec h
    exact h'
  · simpa [Gedges,E] using hc

end
end PlanarUnitDistances
