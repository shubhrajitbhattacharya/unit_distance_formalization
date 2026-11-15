import PlanarUnitDistances.ConditionalFlanks
import PlanarUnitDistances.PartialFlankCharge

namespace PlanarUnitDistances.Flanks
open Set MeasureTheory Real NumberField Finset OAI.PlanarUnitDistances
open scoped Classical
noncomputable section
variable {K I : Type*} [Field K] [NumberField K] [Fintype I]

/-- Data from one interval and the coordinate partitions at one place.
The bit thresholds themselves are fixed by the original field directions. -/
structure LocalComparison (μ : I → ℝ) (d : I → K) (v : AbsoluteValue K ℝ) (ε c : ℝ) where
  lo : ℝ
  hi : ℝ
  globalTail : ℝ → ℝ
  antitone : Antitone globalTail
  direct : I → I → ℝ → Prop
  reciprocal : I → I → ℝ → Prop
  keep : I → I → ℝ → Prop
  flank_nonnegative : ∀i j,i≠j → 0 ≤ BudgetPlaces.alpha v (d i) (d j)+c
  direct_bound : ∀i j s,direct i j s → v (d i-d j)≤exp (-s+c)
  reciprocal_bound : ∀i j s,reciprocal i j s → v ((d i)⁻¹-(d j)⁻¹)≤exp (s+c)
  integrable : ∀i j,i≠j → Integrable (positive lo hi ε (BudgetPlaces.threshold v (d i))
    (BudgetPlaces.threshold v (d j)) globalTail (thresholdTail μ (BudgetPlaces.threshold v ∘ d))
    (direct i j) (reciprocal i j) (keep i j))

namespace LocalComparison
variable {μ : I → ℝ} {d : I → K} {v : AbsoluteValue K ℝ} {ε c : ℝ}

def pairScore (L : LocalComparison μ d v ε c) (i j : I) :=
  let Z := BudgetPlaces.threshold v ∘ d
  (∫s,positive L.lo L.hi ε (Z i) (Z j) L.globalTail (thresholdTail μ Z)
       (L.direct i j) (L.reciprocal i j) (L.keep i j) s)-|Z i-Z j|

def comparison (L : LocalComparison μ d v ε c) :=
  let g := thresholdTail μ (BudgetPlaces.threshold v ∘ d)
  ∫s in commonRegion L.lo L.hi ε L.globalTail,2*g s*(1-g s)

end LocalComparison

def offWeight (μ : I → ℝ) (p : I×I) := if p.1=p.2 then 0 else μ p.1*μ p.2
def offAvg (μ : I → ℝ) (s : I×I → ℝ) := ∑p,offWeight μ p*s p

private theorem off_nonneg (μ : I → ℝ) (hμ : ∀i,0≤μ i) (p : I×I) : 0≤offWeight μ p := by
  unfold offWeight; split_ifs; exact le_rfl; exact mul_nonneg (hμ _) (hμ _)

private theorem local_upper {μ : I → ℝ} (hμ : ∀i,0≤μ i) (total : ∑i,μ i=1)
    {d : I → K} (hn : ∀i,d i≠0) (inj : Function.Injective d) {v ε c} (he : ε≤1/2)
    (L : LocalComparison μ d v ε c) :
    offAvg μ (fun p => L.pairScore p.1 p.2) ≤ L.comparison/15+
      offAvg μ (fun p => BudgetPlaces.flankCharge v c (d p.1) (d p.2)) := by
  have h := iid_distinct_upper v μ hμ total d hn inj he L.globalTail L.antitone
    L.direct L.reciprocal L.keep L.flank_nonnegative L.direct_bound L.reciprocal_bound L.integrable
  have identity : offAvg μ (fun p => L.pairScore p.1 p.2) -
      offAvg μ (fun p => BudgetPlaces.flankCharge v c (d p.1) (d p.2)) =
      ∑i,∑j,if i=j then 0 else μ i*μ j*(L.pairScore i j-BudgetPlaces.flankCharge v c (d i) (d j)) := by
    unfold offAvg
    rw [←Finset.sum_sub_distrib,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    by_cases e : i=j <;> simp [offWeight,e,mul_sub]
  rw [←sub_le_iff_le_add]
  rw [identity]
  change _≤L.comparison/15
  calc
    _ ≤ (1/15:ℝ)*L.comparison := h
    _ = _ := by ring

/-- A nonnegative finite average, counting archimedean places with their
local multiplicities and the stated finite places once. -/
def placeAverage (F : Finset (FinitePlace K)) (a : InfinitePlace K → ℝ) (b : FinitePlace K → ℝ) :=
  ((∑v,(v.mult:ℝ)*a v)+∑v∈F,b v)/(Module.finrank ℚ K:ℝ)

theorem offAvg_placeAverage (F : Finset (FinitePlace K)) (μ : I → ℝ)
    (A : InfinitePlace K → I×I → ℝ) (B : FinitePlace K → I×I → ℝ) :
    placeAverage F (fun v => offAvg μ (A v)) (fun v => offAvg μ (B v)) =
      offAvg μ (fun p => placeAverage F (fun v => A v p) (fun v => B v p)) := by
  unfold placeAverage offAvg
  simp only [mul_div_assoc',mul_add,Finset.mul_sum,←Finset.sum_div,Finset.sum_add_distrib]
  congr 2
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro v _
    ring
  · rw [Finset.sum_comm]

/-- Across every place and every iid pair of distinct neighbors, the price
of including the full score in the conditional experiment is at most
\(2\log 2\) plus one fifteenth of the actual common-level disagreement.
No bound for collisions is used in this off-diagonal assertion. -/
theorem global_distinct_upper (F : Finset (FinitePlace K)) (μ : I → ℝ) (hμ : ∀i,0≤μ i)
    (total : ∑i,μ i=1) (d : I → K) (hn : ∀i,d i≠0) (inj : Function.Injective d)
    (outside : ∀v : FinitePlace K,v∉F → ∀i,v (d i)=1) {ε : ℝ} (he : ε≤1/2)
    (A : ∀v : InfinitePlace K,LocalComparison μ d v.1 ε (log 2))
    (B : ∀v : FinitePlace K,LocalComparison μ d v.1 ε 0) :
    placeAverage F (fun v => offAvg μ (fun p => (A v).pairScore p.1 p.2))
      (fun v => offAvg μ (fun p => (B v).pairScore p.1 p.2)) ≤
        placeAverage F (fun v => (A v).comparison) (fun v => (B v).comparison)/15 + 2*log 2 := by
  let ai (v : InfinitePlace K) (p : I×I) := BudgetPlaces.flankCharge v.1 (log 2) (d p.1) (d p.2)
  let bf (v : FinitePlace K) (p : I×I) := BudgetPlaces.flankCharge v.1 0 (d p.1) (d p.2)
  have offmass : ∑p,offWeight μ p≤1 := calc
    _ ≤ ∑p : I×I,μ p.1*μ p.2 := Finset.sum_le_sum (fun p _ => by
      dsimp [offWeight]; split_ifs; exact mul_nonneg (hμ _) (hμ _); rfl)
    _ = 1 := by rw [Fintype.sum_prod_type]; simp only [←Finset.mul_sum,total,mul_one]
  have bounded : placeAverage F (fun v => offAvg μ (ai v)) (fun v => offAvg μ (bf v)) ≤ 2*log 2 := by
    rw [offAvg_placeAverage]
    unfold offAvg
    calc
      _ ≤ ∑p,offWeight μ p*(2*log 2) := by
        apply Finset.sum_le_sum; intro p _
        by_cases e : p.1=p.2
        · simp only [offWeight,e,if_true,zero_mul,le_refl]
        · exact mul_le_mul_of_nonneg_left (BudgetPlaces.partial_flank_charge F (hn _) (hn _)
            (inj.ne e) (fun v hv => ⟨outside v hv _,outside v hv _⟩)) (off_nonneg μ hμ p)
      _ ≤ _ := by
        rw [←Finset.sum_mul]
        simpa using mul_le_mul_of_nonneg_right offmass
          (mul_nonneg (by norm_num : (0:ℝ)≤2) (Real.log_nonneg (by norm_num : (1:ℝ)≤2)))
  have ia := Finset.sum_le_sum (s:=Finset.univ) (fun (v : InfinitePlace K) _ =>
    mul_le_mul_of_nonneg_left (local_upper hμ total hn inj he (A v)) (Nat.cast_nonneg v.mult))
  have fb := Finset.sum_le_sum (s:=F) (fun (v : FinitePlace K) _ => local_upper hμ total hn inj he (B v))
  have raw := div_le_div_of_nonneg_right (add_le_add ia fb) (Nat.cast_nonneg (α:=ℝ) (Module.finrank ℚ K))
  apply raw.trans
  apply le_trans _ (add_le_add (le_refl _) bounded)
  unfold placeAverage
  simp only [mul_add,Finset.sum_add_distrib,mul_div_assoc',←Finset.sum_div]
  dsimp only [ai,bf]
  ring_nf <;> exact le_rfl

end
end PlanarUnitDistances.Flanks
