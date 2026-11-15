import PlanarUnitDistances.RecordBaseDiagonal
import PlanarUnitDistances.RecordComparison

namespace OAI.PlanarUnitDistances.PhysicalLevels
open MeasureTheory FiniteLaw Finset StarScore FiniteStarCoupling
open _root_.PlanarUnitDistances.Flanks
open scoped Classical
noncomputable section
variable {P Q B I : Type*} [Fintype P] [Fintype Q] [Fintype B] [Fintype I]

private lemma avg_mono_positive (β : Law B) {f g : B → ℝ}
    (h : ∀b,0<β.val b → f b≤g b) : avg β f ≤ avg β g := by
  apply sum_le_sum; intro b _
  rcases (β.nonneg b).eq_or_lt with zero|positive
  · rw [←zero]; simp
  · exact mul_le_mul_of_nonneg_left (h b positive) positive.le

/-- Average over the actual base (which may already contain a conditioning
list). An off-diagonal bound is needed only on bases of positive mass.
The diagonal stays weighted by the exceptional width of that same base. -/
theorem average_base_scores (π : Law (P×Q)) (ν : Measure (Record P Q)) [IsFiniteMeasure ν]
    (β : Law B) (μ : B → Law I) (edge : B → I → P×Q) (base : B → P⊕Q)
    (neighbors : B → I → P⊕Q) (l : Record P Q → Finset (P⊕Q)×Finset (P⊕Q)) (ε : ℝ)
    (off : ∀b,0 < β.val b →
      offAvg (μ b).val (fun ij => ∫t,baseSlot π (μ b) (edge b) (base b) (neighbors b) l ij.1 ij.2 t ∂ν) ≤
        (∫t,variation (μ b) (fun i => t.bit (edge b i).1 (edge b i).2) ∂commonLaw π ν)/15+2*Real.log 2)
    (collision : 2*Real.log 2+avg β (fun b =>
      2*(width ν (common π)+baseExceptionWidth π ν l (base b))*(∑i,((μ b).val i)^2))≤ε) :
    avg β (fun b => avg (pair (μ b) (μ b)) (fun ij =>
        ∫t,baseSlot π (μ b) (edge b) (base b) (neighbors b) l ij.1 ij.2 t ∂ν)) ≤
      (∫t,avg β (fun b => variation (μ b) (fun i => t.bit (edge b i).1 (edge b i).2)) ∂commonLaw π ν)/15+ε := by
  let V (b : B) := ∫t,variation (μ b) (fun i => t.bit (edge b i).1 (edge b i).2) ∂commonLaw π ν
  let D (b : B) := 2*(width ν (common π)+baseExceptionWidth π ν l (base b))*(∑i,((μ b).val i)^2)
  let A (b : B) := avg (pair (μ b) (μ b)) (fun ij =>
    ∫t,baseSlot π (μ b) (edge b) (base b) (neighbors b) l ij.1 ij.2 t ∂ν)
  have bound : avg β A ≤ avg β (fun b => (1/15:ℝ)*V b + 2*Real.log 2+D b) := by
    apply avg_mono_positive
    intro b hb
    have diagonal := base_all_upper π ν (μ b) (edge b) (base b) (neighbors b) l
    dsimp only at diagonal
    change A b ≤ _ + D b at diagonal
    have pos := off b hb
    change _ ≤ V b/15+2*Real.log 2 at pos
    linarith only [diagonal,pos]
  rw [avg_add,avg_add,avg_const,avg_smul] at bound
  rw [FiniteLawIntegral.integral_avg _ _ (fun _ => Integrable.of_finite)]
  change avg β A ≤ avg β V/15+ε
  change 2*Real.log 2 + avg β D ≤ ε at collision
  linarith only [bound,collision]

end
end OAI.PlanarUnitDistances.PhysicalLevels
