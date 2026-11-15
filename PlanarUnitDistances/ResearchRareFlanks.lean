import PlanarUnitDistances.ResearchFlankCoordinates
import PlanarUnitDistances.FixedPairRecord

namespace PlanarUnitDistances.ResearchPhysical
open Competition Competition.IncidencePiece Real NumberField Finset Set
open OAI.PlanarUnitDistances.BudgetPlaces
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

theorem record_threshold (M : IncidencePiece K) (u : InfinitePlace K→ℝ) (v : Place K)
    (s : ℝ) (e : Competition.Plane×Competition.Plane) (he : e∈M.E) :
    (M.recordsAt u v s).bit e=decide (s<M.threshold (valuation v) e) := by
  cases v with
  | inl v => exact M.arch_bit v _ _ s e he
  | inr v => exact M.finite_edge_bit v s e he

def bitFrequency (M : IncidencePiece K) (v : Place K) (s : ℝ) :=
  M.edgeProb (fun e => s<M.threshold (valuation v) e)

theorem frequency_antitone (M : IncidencePiece K) (v : Place K) : Antitone (bitFrequency M v) := by
  intro s t hst
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have sub : M.E.filter (fun e => t<M.threshold (valuation v) e) ⊆ M.E.filter (fun e => s<M.threshold (valuation v) e) := by
    intro e he
    exact mem_filter.mpr ⟨(mem_filter.mp he).1,hst.trans_lt (mem_filter.mp he).2⟩
  exact_mod_cast Finset.card_le_card sub

private lemma freq_congr (M : IncidencePiece K) (a b : Competition.Plane×Competition.Plane → Prop)
    (h : ∀e∈M.E,a e ↔ b e) : M.edgeProb a=M.edgeProb b := by
  unfold edgeProb
  rw [filter_congr h]

theorem minority_frequency (M : IncidencePiece K) (u : InfinitePlace K→ℝ) (v : Place K)
    (he : 0<(M.E.card:ℝ)) (s : ℝ) :
    let r := M.recordsAt u v s
    M.minorityMass r = if r.majority then 1-bitFrequency M v s else bitFrequency M v s := by
  let r := M.recordsAt u v s
  change M.edgeProb (fun e => r.bit e ≠ r.majority)=_
  cases hm : r.majority with
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    apply freq_congr
    intro e h
    rw [show r.bit e=decide (s<M.threshold (valuation v) e) from record_threshold M u v s e h]
    simp
  | true =>
    simp only [ite_true]
    let a := fun e => s<M.threshold (valuation v) e
    have hc := freq_congr M (fun e => r.bit e≠true) (fun e => ¬a e) (fun e h => by
      rw [show r.bit e=decide (s<M.threshold (valuation v) e) from record_threshold M u v s e h]
      simp [a])
    rw [hc]
    have comp (f : Competition.Plane×Competition.Plane→Prop) : M.edgeProb (fun e => ¬f e)=1-M.edgeProb f := by
      have n := congrArg (fun j : ℕ => (j:ℝ)/M.E.card) (@card_filter_add_card_filter_not _ M.E f
        (fun e => Classical.propDecidable (f e)) (fun e => Classical.propDecidable (¬f e)))
      simp only [Nat.cast_add,add_div,div_self he.ne'] at n
      unfold edgeProb
      linarith only [n]
    exact comp a

theorem flank_length_nonneg (M : IncidencePiece K) {p q r : Competition.Plane}
    (he : (p,q)∈M.E) (he' : (p,r)∈M.E) (hne : q≠r) (v : Place K) :
    0≤alpha (valuation v) (jump M p q) (jump M p r)+flankConstant v := by
  cases v with
  | inl v => exact alpha_add_log_two_nonneg v.val (jump_ne M he) (jump_ne M he') (distinct_jumps M he he' hne)
  | inr v =>
    change 0≤alpha v.val _ _+0
    rw [add_zero]
    apply alpha_nonneg_nonarch v.val _ (jump_ne M he) (jump_ne M he') (distinct_jumps M he he' hne)
    intro x y
    change v (x+y) ≤ max (v x) (v y)
    simp_rw [←v.norm_embedding_eq,FinitePlace.norm_embedding]
    exact NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v.maximalIdeal x y

/-- Positive rare score forces exactly the lower or upper geometric flank,
according to the physical majority bit. -/
theorem rare_flanks (M : IncidencePiece K) (u : InfinitePlace K→ℝ) (v : Place K)
    (d : CoordinateLevel M.Label→M.Label) {p q r : Competition.Plane}
    (he : (p,q)∈M.E) (he' : (p,r)∈M.E) (hne : q≠r)
    (hord : M.threshold (valuation v) (p,q)≤M.threshold (valuation v) (p,r)) (s : ℝ)
    (hp : M.rarePairPositive d p q r (M.recordsAt u v s)≠0) :
    let t := M.recordsAt u v s
    let b := M.threshold (valuation v) (p,q)
    let b' := M.threshold (valuation v) (p,r)
    let T := alpha (valuation v) (jump M p q) (jump M p r)+flankConstant v
    (t.majority=false → s∈Icc (b-T) b ∧ bitFrequency M v s<eps) ∧
    (t.majority=true → s∈Icc b' (b'+T) ∧ 1-eps<bitFrequency M v s) := by
  let t := M.recordsAt u v s
  have facts : M.goodRare t ∧ t.selected p≠d t ∧ t.bit (p,q)≠t.majority ∧
      t.bit (p,r)≠t.majority ∧ t.selected q=t.selected r := by
    by_contra hn; exact hp (ite_eq_right hn)
  obtain ⟨good,_,bit1,bit2,mat⟩ := facts
  have pos : 0<(M.E.card:ℝ) := by exact_mod_cast card_pos.mpr ⟨_,he⟩
  have minor := minority_frequency M u v pos s
  have freq : M.minorityMass t<eps := good.1
  have geom := coordinate_matches M u v s q r (mem_union_right _ (mem_product.mp (M.membership he)).2)
    (mem_union_right _ (mem_product.mp (M.membership he')).2)
  have b1 : t.bit (p,q)=decide (s<M.threshold (valuation v) (p,q)) := record_threshold M u v s _ he
  have b2 : t.bit (p,r)=decide (s<M.threshold (valuation v) (p,r)) := record_threshold M u v s _ he'
  have dd := distinct_jumps M he he' hne
  constructor
  · intro hm
    change t.majority=false at hm
    have cell : (t.label q).2=(t.label r).2 := by simpa [CoordinateLevel.selected,hm] using mat
    have hm' := geom.2 cell
    have reciprocal : (valuation v) ((jump M p q)⁻¹-(jump M p r)⁻¹)≤exp (s+flankConstant v) := by
      rwa [jump_inverse M he,jump_inverse M he',
        show (M.W p-M.W q)-(M.W p-M.W r)=-(M.W q-M.W r) by ring,(valuation v).map_neg]
    have hs : s<M.threshold (valuation v) (p,q) := by simpa [hm,b1] using bit1
    refine ⟨reciprocal_match_lower_flank (valuation v) (jump_ne M he) (jump_ne M he') dd hord hs reciprocal,?_⟩
    change M.minorityMass t=(if t.majority then _ else _) at minor
    simpa only [minor,hm,Bool.false_eq_true,ite_false] using freq
  · intro hm
    change t.majority=true at hm
    have cell : (t.label q).1=(t.label r).1 := by simpa [CoordinateLevel.selected,hm] using mat
    have dir : (valuation v) (jump M p q-jump M p r)≤exp (-s+flankConstant v) := by
      rw [show jump M p q-jump M p r=-(M.Z q-M.Z r) by unfold jump; ring,(valuation v).map_neg]
      exact geom.1 cell
    have hs : M.threshold (valuation v) (p,r) ≤ s := by simpa [hm,b2] using bit2
    refine ⟨direct_match_upper_flank (valuation v) dd hord hs dir,?_⟩
    change M.minorityMass t=(if t.majority then _ else _) at minor
    rw [minor,hm] at freq
    simp only [ite_true] at freq
    linarith

end
end PlanarUnitDistances.ResearchPhysical

