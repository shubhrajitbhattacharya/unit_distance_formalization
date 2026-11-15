import PlanarUnitDistances.ResearchCommonDisagreement
import PlanarUnitDistances.ResearchThresholds
import PlanarUnitDistances.UniformPhysical
import PlanarUnitDistances.RecordComparison

namespace PlanarUnitDistances.ResearchPhysical
open Finset Set NumberField MeasureTheory OAI.PlanarUnitDistances OAI.PlanarUnitDistances.CircleIncidence
open UniformNormalization BoundedHeight FiniteLaw FiniteStarCoupling StarScore CommonFieldModel
open UniformPhysical PhysicalLevels ComparisonConstants Competition.IncidencePiece
open scoped Classical
noncomputable section
variable {P Q : Finset Competition.Plane}

private lemma mem_rows (p : P) (q : Q) : p ∈ unitRows P Q q ↔ dist p.val q.val=1 := by
  simp [unitRows,unitNeighbors]

private lemma sampled_event (M : Model P Q) (he : 0 < incidences P Q)
    (A : Competition.Plane × Competition.Plane → Prop) (b : P → Q → Bool)
    (agree : ∀ p q, dist p.val q.val=1 → (A (p.val,q.val) ↔ b p q=true)) :
    (toPiece M).edgeProb A = event (incidenceLaw P Q he) (fun x => b x.1 x.2=true) := by
  rw [edgeProb_eq_sum]
  unfold event avg
  apply sum_congr rfl
  rintro ⟨p,q⟩ _
  change _ = weight (unitRows P Q) (incidences P Q) p q * _
  by_cases h : dist p.val q.val=1
  · by_cases a : A (p.val,q.val) <;> simp_all [weight,mem_rows,agree p q h]
  · simp [h,weight,mem_rows]

private lemma variation_congr (he : 0 < incidences P Q) (hq : ∀ q : Q, 0 < degree P q)
    (a b : P → Q → Bool) (same : ∀ p q, dist p.val q.val=1 → a p q=b p q) :
    VQ (incidenceLaw P Q he) a = VQ (incidenceLaw P Q he) b := by
  let π := incidenceLaw P Q he
  apply avg_congr
  intro q
  have pos : 0 < (right π).val q := by
    rw [edge_right,centerLaw,unitRows_center_degree]; exact div_pos (hq q) he
  unfold variation
  suffices freq : frequency (col π q) (fun p => a p q) = frequency (col π q) (fun p => b p q) by rw [freq]
  unfold frequency event avg
  apply sum_congr rfl
  intro p _
  by_cases d : dist p.val q.val=1
  · by_cases bit : b p q = true <;> simp [same p q d,bit]
  · have hz : (col π q).val p=0 := by
      rw [col_val π pos p]
      change weight (unitRows P Q) (incidences P Q) p q / _ = 0
      simp [weight,mem_rows,d]
    simp [hz]

private lemma eps_eq : Competition.eps = dy 1800 := by
  unfold Competition.eps dy
  rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
  norm_cast

private lemma common_level (M : Model P Q) (he : 0 < incidences P Q)
    (hq : ∀ q : Q, 0 < degree P q) (v : AbsoluteValue M.field ℝ) (s : ℝ)
    (b : CoordinateLevel (toPiece M).Label) (t : Record P Q)
    (minor : (toPiece M).minorityMass b = (toPiece M).frequencyMinority (fun x => v x) s)
    (bit : ∀ e ∈ (toPiece M).E, b.bit e = decide (s < (toPiece M).threshold (fun x => v x) e))
    (thresholds : ∀ (p : P) (q : Q), t.bit p q = decide (s < -Real.log (v (M.z (.inl p)-M.z (.inr q))))) :
    (toPiece M).commonDisagreement b =
      if PhysicalLevels.common (incidenceLaw P Q he) t then VQ (incidenceLaw P Q he) t.bit else 0 := by
  have bound (p : P) (q : Q) :
      (toPiece M).threshold (fun x => v x) (p.val,q.val) = -Real.log (v (M.z (.inl p)-M.z (.inr q))) := by
    unfold Competition.IncidencePiece.threshold; rw [z_point,z_center]
  have eqv (p : P) (q : Q) : (s < (toPiece M).threshold (fun x => v x) (p.val,q.val)) ↔ t.bit p q=true := by
    rw [thresholds,bound]; simp
  have em := sampled_event M he (fun e => s < (toPiece M).threshold (fun x => v x) e) t.bit (fun p q _ => eqv p q)
  have hm : (toPiece M).minorityMass b = PhysicalLevels.minority (incidenceLaw P Q he) t := by
    rw [minor]; unfold frequencyMinority PhysicalLevels.minority; rw [em]
  have same (p : P) (q : Q) (d : dist p.val q.val=1) : b.bit (p.val,q.val)=t.bit p q := by
    rw [bit _ (full M p.val p.prop q.val q.prop d),thresholds,bound]
  rw [common_disagreement_eq M he hq b,hm,eps_eq]
  unfold PhysicalLevels.common
  rw [variation_congr he hq _ _ same]

private lemma fin_bit (M : Model P Q) (v : FinitePlace M.field) (s : ℝ)
    (e : Competition.Plane × Competition.Plane) (h : e∈(toPiece M).E) :
    ((toPiece M).finiteRecord v s).bit e=decide (s < (toPiece M).threshold (fun x => v x) e) := by
  change (if _ : e∈(toPiece M).E then decide (s < (toPiece M).threshold (fun x => v x) e) else false) = _
  simp [h]

/-- The posterior integral and the physical error budget integrate exactly the same
common disagreement. The two archimedean shifts in the posterior are arbitrary. -/
theorem common_integral_on_windows_eq (M : Model P Q) (he : 0 < incidences P Q)
    (hq : ∀ q : Q, 0 < degree P q) (F : Finset (FinitePlace M.field))
    (l h : AbsoluteValue M.field ℝ → ℝ) (u : InfinitePlace M.field → ℝ)
    (U V : InfinitePlace M.field → ℝ × ℝ) :
    let π := incidenceLaw P Q he
    (toPiece M).placeIntegral F l h u (toPiece M).commonDisagreement =
      ∫ t, VQ π t.bit ∂commonLaw π (PhysicalLevels.measure F M.z M.w U V
        (fun v => l v.1) (fun v => h v.1) (fun v => l v.1) (fun v => h v.1)) := by
  let π := incidenceLaw P Q he
  let mask (t : Record P Q) := if PhysicalLevels.common π t then VQ π t.bit else 0
  have ep : 0 < ((toPiece M).E.card : ℝ) := by rwa [Research.edge_count _ (full M)]
  have a (v : InfinitePlace M.field) (s : ℝ) :
      (toPiece M).commonDisagreement ((toPiece M).archRecord v (u v,u v) (u v,u v) s) =
      mask (arch v (U v) (V v) M.z M.w s) :=
    common_level M he hq v.1 s _ _ (arch_minority _ ep v _ _ s)
      (arch_bit _ v _ _ s) (fun _ _ => rfl)
  have f (v : FinitePlace M.field) (s : ℝ) :
      (toPiece M).commonDisagreement ((toPiece M).finiteRecord v s) =
      mask (PhysicalLevels.finite v M.z M.w s) :=
    common_level M he hq v.1 s _ _ (finite_minority _ ep v s)
      (fin_bit M v s) (fun _ _ => rfl)
  dsimp only
  rw [commonLaw,←integral_indicator (Set.toFinite _).measurableSet]
  change _ = ∫ t, mask t ∂PhysicalLevels.measure F M.z M.w U V
    (fun v => l v.1) (fun v => h v.1) (fun v => l v.1) (fun v => h v.1)
  unfold placeIntegral
  rw [integral_measure]
  simp_rw [a,f]

/-- In particular the original common-center walk uses the posterior comparison
on its own support and its own symmetric profile intervals. -/
theorem common_integral_eq (M : Model P Q) (he : 0 < incidences P Q)
    (hq : ∀ q : Q, 0 < degree P q) (u : InfinitePlace M.field → ℝ)
    (U V : InfinitePlace M.field → ℝ × ℝ) :
    let rows := unitRows P Q
    let r := profileRadius rows M.z M.w
    let π := incidenceLaw P Q he
    (toPiece M).placeIntegral (primes rows M.z M.w) (fun v => -r v) r u (toPiece M).commonDisagreement =
      ∫ t, VQ π t.bit ∂commonLaw π (fullMeasure rows M.z M.w U V) :=
  common_integral_on_windows_eq M he hq _ _ _ u U V

end
end PlanarUnitDistances.ResearchPhysical
