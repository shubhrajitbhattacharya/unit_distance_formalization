import PlanarUnitDistances.ResearchWalkMoments

namespace PlanarUnitDistances
open Filter OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open scoped Topology Classical
noncomputable section

/-- Dense extraction with a lower bound on the selected graph's own scale. -/
def DenseGraphExtractionAtScale (δ minScale : ℝ) : Prop :=
  let g := 3*δ
  let a := 10000*g
  ∃ k : ℝ, 0 < k ∧ ∀ᶠ n : ℕ in atTop, ∀ X : Finset Plane,
    X.card = n → AlgebraicPoints X →
    (n:ℝ)^(4/3-δ) ≤ ((orderedPairs X).card : ℝ) →
    ∃ (N : ℕ) (K : Type) (_ : Field K) (_ : NumberField K) (G : AdmissibleGraph N K),
      minScale ≤ G.scale ∧ 2^10000 ≤ N ∧ (N:ℝ) ≤ 2 * (incidenceScale n)^(1+2*a) ∧
      k * (incidenceScale n)^(2+3*a-180*g) ≤ (G.edges.card : ℝ)


namespace ProofAssembly

/-- The same retained point set and the exact quantitative lower bound for the
scale chosen on its own common-field model. -/
def LargePieceGraphWithScale : Prop :=
  let g := 3*exactGap
  let a := 10000*g
  ∃ k : ℝ, 0 < k ∧ ∀ᶠ t : ℝ in atTop,
    ∀ (P Q : Finset Plane) (M : CommonFieldModel.Model P Q), LargePiece t P Q M →
      ∃ G : AdmissibleGraph P.card M.field, G.points=P ∧ pieceScale M/500 ≤ G.scale ∧
        k*t^(2+3*a-180*g) ≤ (G.edges.card:ℝ)


theorem large_piece_graph_with_scale : LargePieceGraphWithScale := by
  let g := 3*exactGap
  let a := 10000*g
  have hε : 0 < comparisonEpsilon := by unfold comparisonEpsilon; positivity
  refine ⟨comparisonEpsilon*(27/50)/32000,by positivity,?_⟩
  filter_upwards [ResearchPhysical.original_walk_moments,rich_circle_survival hε,eventually_gt_atTop (0:ℝ)] with t moments survive ht
  intro P Q M piece
  obtain ⟨J,V,H,scale,hJ,hV,raw,good⟩ :=
    before_circle_deletion_at_scale_of_moments M ht piece (moments P Q M piece)
  let C := removeRichPairs H
  have hm := survive P Q M piece H raw
  have hC (z) (q) (hq : q ∈ C z) := by
    obtain ⟨mem,safe⟩ := (mem_removeRichPairs H z q).mp hq
    obtain ⟨dif,hp,hr,height,error⟩ := good z q mem
    exact And.intro dif (And.intro hp (And.intro hr (And.intro height (And.intro error safe))))
  obtain ⟨hPal,_,_,_,hedge,_,_,degQ,_,_,_⟩ := piece
  let d : ℝ := (27/50)*t^(a-90*g)
  have hd : 0<d := mul_pos (by norm_num) (Real.rpow_pos_of_pos ht _)
  have hmin (q : Q) : d ≤ ((unitRows P Q q).card:ℝ) := by
    rw [unitRows_center_degree]
    exact (degQ q q.prop).1
  obtain ⟨G,hP,hG,hcount⟩ := graph_of_surviving_triples hPal M C V hV J d comparisonEpsilon hJ hd
    hmin ((Real.rpow_pos_of_pos ht _).trans_le hedge) hm hC
  refine ⟨G,hP,scale.trans_eq hG.symm,le_trans ?_ hcount⟩
  have eq : t^(2+3*a-180*g)=t^(2+2*a-90*g)*t^(a-90*g) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  rw [eq]
  dsimp [d]
  calc
    _ = comparisonEpsilon*t^(2+2*a-90*g)*((27/50)*t^(a-90*g))/32000 := by ring
    _ ≤ _ := by gcongr


/-- Unconditional dense extraction at the manuscript exponent. The same
graph satisfies the edge lower bound and the stronger scale lower bound. -/
theorem original_extraction_at_large_scale :
    DenseGraphExtractionAtScale exactGap ((2:ℝ)^2100/500) := by
  let g := 3*exactGap
  let a := 10000*g
  obtain ⟨k,hk,hle⟩ := large_piece_graph_with_scale
  refine ⟨k,hk,?_⟩
  have ht : Tendsto incidenceScale atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0<(1/3:ℝ))).comp tendsto_natCast_atTop_atTop
  have hg : 0<g := mul_pos (by norm_num) exactGap_pos
  have expPos : 0<1+2*a-173*g := by dsimp [a]; linarith
  have hb := (tendsto_rpow_atTop expPos).eventually_ge_atTop ((2:ℝ)^10000)
  filter_upwards [ht.eventually dense_to_large_piece,ht.eventually hle,ht.eventually hb] with n hp he hs
  intro X hX _hAlg hcount
  let t := incidenceScale n
  have ht3 : (n:ℝ)=t^3 := by
    change (n:ℝ)=((n:ℝ)^(1/3:ℝ))^3
    rw [← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hpow : t^(4-g)=(n:ℝ)^(4/3-exactGap) := by
    dsimp [t,incidenceScale,g]
    rw [← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  obtain ⟨P,Q,M,piece⟩ := hp X (by rw [hX]; exact ht3) (hpow ▸ hcount)
  obtain ⟨G,_,scale,hG⟩ := he P Q M piece
  have big : (2:ℝ)^2100 < pieceScale M := piece.2.2.2.2.2.2.2.2.2.2
  refine ⟨P.card,M.field,inferInstance,inferInstance,G,?_,?_,piece.2.2.1,hG⟩
  · exact (div_le_div_of_nonneg_right big.le (by norm_num : (0:ℝ) ≤ 500)).trans scale
  exact_mod_cast hs.trans piece.2.1


end ProofAssembly
end
end PlanarUnitDistances
