import PlanarUnitDistances.RareCoordinateLevels
import PlanarUnitDistances.SelectedDirections
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Function.Floor

namespace PlanarUnitDistances.Competition.IncidencePiece
open Finset MeasureTheory NumberField Real
open scoped Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

abbrev Vertices (M : IncidencePiece K) := ↥(M.P∪M.Q)
abbrev Label (M : IncidencePiece K) := Finset M.Vertices
abbrev RawLevel (M : IncidencePiece K) := (M.Vertices → M.Label×M.Label) × (M.E → Bool)

def threshold (M : IncidencePiece K) (v : K → ℝ) (e : Plane×Plane) :=
  -Real.log (v (M.Z e.1-M.Z e.2))

private def readBits (M : IncidencePiece K) (b : M.E → Bool) (e : Plane×Plane) :=
  if h : e∈M.E then b ⟨e,h⟩ else false

private def realize (M : IncidencePiece K) (r : M.RawLevel) : CoordinateLevel M.Label where
  label p := if h : p∈M.P∪M.Q then r.1 ⟨p,h⟩ else (∅,∅)
  bit := readBits M r.2
  majority := decide (1/2<M.edgeProb (fun e => readBits M r.2 e=true))

private def measurableRecord (M : IncidencePiece K) (v : K → ℝ)
    (labels : ℝ → M.Vertices → M.Label×M.Label) (hl : Measurable labels) :
    SimpleFunc ℝ (CoordinateLevel M.Label) := by
  let b (s : ℝ) (e : M.E) : Bool := decide (s<M.threshold v e.val)
  have hb : Measurable b := by
    apply measurable_pi_iff.mpr
    intro e
    have h : MeasurableSet {s : ℝ | s<M.threshold v e.val} := measurableSet_Iio
    have eq : (fun s => b s e)=fun s => if s<M.threshold v e.val then true else false := by
      funext s; by_cases hs : s<M.threshold v e.val <;> simp [b,hs]
    rw [eq]
    exact Measurable.ite h measurable_const measurable_const
  let raw : ℝ → M.RawLevel := fun s => (labels s,b s)
  let f : SimpleFunc ℝ M.RawLevel := ⟨raw,fun r => (hl.prodMk hb) (measurableSet_singleton r),Set.toFinite _⟩
  exact f.map (realize M)

private lemma edgeProb_congr (M : IncidencePiece K) (A B : Plane×Plane → Prop)
    (h : ∀e∈M.E,A e ↔ B e) : M.edgeProb A=M.edgeProb B := by
  unfold edgeProb
  exact congrArg (fun X : Finset (Plane×Plane) => (X.card:ℝ)/M.E.card) (filter_congr h)

private lemma complement (M : IncidencePiece K) (he : 0<(M.E.card:ℝ)) (A : Plane×Plane → Prop) :
    M.edgeProb (fun e => ¬A e)=1-M.edgeProb A := by
  have eq := congrArg (fun n : ℕ => (n:ℝ)/M.E.card) (@Finset.card_filter_add_card_filter_not _
    M.E A (fun e => Classical.propDecidable (A e)) (fun e => Classical.propDecidable (¬A e)))
  simp only [Nat.cast_add,add_div,div_self he.ne'] at eq
  unfold edgeProb; linarith only [eq]

private lemma raw_minority (M : IncidencePiece K) (r : M.RawLevel) (he : 0<(M.E.card:ℝ)) :
    M.minorityMass (realize M r) =
      let h := M.edgeProb (fun e => readBits M r.2 e=true); min h (1-h) := by
  let h := M.edgeProb (fun e => readBits M r.2 e=true)
  by_cases hm : 1/2<h
  · have maj : (realize M r).majority=true := decide_eq_true hm
    rw [minorityMass,maj]
    exact (complement M he (fun e => readBits M r.2 e=true)).trans
      (min_eq_right (show 1-h≤h by linarith)).symm
  · have maj : (realize M r).majority=false := decide_eq_false hm
    rw [minorityMass,maj]
    refine (edgeProb_congr M _ _ (fun e _ => show (readBits M r.2 e≠false) ↔ readBits M r.2 e=true by cases readBits M r.2 e <;> simp)).trans ?_
    exact (min_eq_left (show h≤1-h by linarith)).symm

private lemma cell_measurable (M : IncidencePiece K) (rel : ℝ → M.Vertices → M.Vertices → Prop)
    (hm : ∀p q,MeasurableSet {s | rel s p q}) :
    Measurable (fun s p => univ.filter (rel s p)) := by
  apply measurable_pi_iff.mpr
  intro p
  apply measurable_finset_iff.mpr
  intro q
  apply measurableSet_setOfPred.mp
  simpa only [mem_filter,mem_univ,true_and] using hm p q

private lemma cell_eq {V : Type*} [Fintype V] (r : V → V → Prop) (hr : Equivalence r) (p q : V) :
    univ.filter (r p)=univ.filter (r q) ↔ r p q := by
  constructor
  · intro h
    have mem : q∈univ.filter (r q) := mem_filter.mpr ⟨mem_univ _,hr.refl _⟩
    exact (mem_filter.mp (h ▸ mem : q∈univ.filter (r p))).2
  · intro h
    ext j
    simp only [mem_filter,mem_univ,true_and]
    exact ⟨hr.trans (hr.symm h),hr.trans h⟩

private def ball (M : IncidencePiece K) (v : FinitePlace K) (z : Plane → K) (s : ℝ)
    (p q : M.Vertices) : Prop := v (z p.val-z q.val)≤exp s

private lemma ball_eq (M : IncidencePiece K) (v : FinitePlace K) (z : Plane → K) (s : ℝ) :
    Equivalence (ball M v z s) := by
  have ul (a b : K) : v (a+b)≤max (v a) (v b) := by
    simp_rw [←v.norm_embedding_eq,FinitePlace.norm_embedding]
    exact NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v.maximalIdeal a b
  constructor
  · intro p; simp [ball,(exp_pos s).le]
  · intro p q h
    change v (z p.val-z q.val)≤exp s at h
    change v (z q.val-z p.val)≤exp s
    rw [←neg_sub (z p.val) (z q.val),map_neg_eq_map]
    exact h
  · intro p q u hp hq
    calc
      v (z p.val-z u.val) = v ((z p.val-z q.val)+(z q.val-z u.val)) := by rw [sub_add_sub_cancel]
      _ ≤ _ := ul _ _
      _ ≤ _ := max_le hp hq

/-- Index of the translated square of side exp(s) containing the chosen
coordinate of a plane vertex at its infinite place. -/
def grid (v : InfinitePlace K) (z : Plane → K) (u : ℝ×ℝ) (s : ℝ) (p : Plane) : ℤ×ℤ :=
  (⌊(v.embedding (z p)).re/exp s+u.1⌋,⌊(v.embedding (z p)).im/exp s+u.2⌋)

private def grids (M : IncidencePiece K) (v : InfinitePlace K) (z : Plane → K) (u : ℝ×ℝ) (s : ℝ)
    (p q : M.Vertices) : Prop := grid v z u s p.val=grid v z u s q.val

/-- The actual square-grid cells at an infinite place and the actual unit-edge
threshold bits form a measurable finite-range record as the real level varies. -/
def archRecord (M : IncidencePiece K) (v : InfinitePlace K) (u w : ℝ×ℝ) :
    SimpleFunc ℝ (CoordinateLevel M.Label) :=
  measurableRecord M v (fun s p => (univ.filter (grids M v M.Z u (-s) p),univ.filter (grids M v M.W w s p))) (by
    have mg (z : Plane → K) (u : ℝ×ℝ) (p : Plane) : Measurable (fun s => grid v z u s p) := by unfold grid; fun_prop
    have ml (z : Plane → K) (u : ℝ×ℝ) := cell_measurable M (grids M v z u)
      (fun p q => measurableSet_eq_fun (mg z u p.val) (mg z u q.val))
    exact measurable_pi_iff.mpr (fun p => (((measurable_pi_iff.mp (ml M.Z u) p).comp measurable_neg).prodMk
      (measurable_pi_iff.mp (ml M.W w) p))))

/-- At a finite place the two cells are the actual ultrametric balls of
radii exp(-s) and exp(s), on the same finite set of all vertices. -/
def finiteRecord (M : IncidencePiece K) (v : FinitePlace K) :
    SimpleFunc ℝ (CoordinateLevel M.Label) :=
  measurableRecord M v (fun s p => (univ.filter (ball M v M.Z (-s) p),univ.filter (ball M v M.W s p))) (by
    have ml (z : Plane → K) := cell_measurable M (ball M v z)
      (fun _ _ => measurableSet_le measurable_const measurable_exp)
    exact measurable_pi_iff.mpr (fun p => (((measurable_pi_iff.mp (ml M.Z) p).comp measurable_neg).prodMk
      (measurable_pi_iff.mp (ml M.W) p))))

private lemma record_bit (M : IncidencePiece K) (v : K → ℝ) (lab : ℝ → M.Vertices → M.Label×M.Label)
    (hl : Measurable lab) (s : ℝ) (e : Plane×Plane) (h : e∈M.E) :
    ((measurableRecord M v lab hl) s).bit e=decide (s<M.threshold v e) := by
  change readBits M _ e=_
  simp [readBits,h]

private lemma record_label (M : IncidencePiece K) (v : K → ℝ) (lab : ℝ → M.Vertices → M.Label×M.Label)
    (hl : Measurable lab) (s : ℝ) (p : Plane) (hp : p∈M.P∪M.Q) :
    ((measurableRecord M v lab hl) s).label p=lab s ⟨p,hp⟩ := by
  change (if h : p∈M.P∪M.Q then lab s ⟨p,h⟩ else (∅,∅))=_
  rw [dite_eq_left hp]

theorem arch_bit (M : IncidencePiece K) (v : InfinitePlace K) (u w : ℝ×ℝ) (s : ℝ)
    (e : Plane×Plane) (he : e∈M.E) : (archRecord M v u w s).bit e=decide (s<M.threshold v e) :=
  record_bit M v _ _ s e he

theorem arch_matches (M : IncidencePiece K) (v : InfinitePlace K) (u w : ℝ×ℝ) (s : ℝ)
    (p q : Plane) (hp : p∈M.P∪M.Q) (hq : q∈M.P∪M.Q) :
    let r := archRecord M v u w s
    ((r.label p).1=(r.label q).1 ↔ grid v M.Z u (-s) p=grid v M.Z u (-s) q) ∧
    ((r.label p).2=(r.label q).2 ↔ grid v M.W w s p=grid v M.W w s q) := by
  dsimp only
  unfold archRecord
  rw [record_label M v _ _ s p hp,record_label M v _ _ s q hq]
  have rel (z : Plane → K) (u : ℝ×ℝ) (x : ℝ) : Equivalence (grids M v z u x) :=
    ⟨fun _ => rfl,fun a => a.symm,fun a b => a.trans b⟩
  exact ⟨cell_eq _ (rel M.Z u (-s)) _ _,cell_eq _ (rel M.W w s) _ _⟩

theorem finite_matches (M : IncidencePiece K) (v : FinitePlace K) (s : ℝ)
    (p q : Plane) (hp : p∈M.P∪M.Q) (hq : q∈M.P∪M.Q) :
    let r := finiteRecord M v s
    ((r.label p).1=(r.label q).1 ↔ v (M.Z p-M.Z q)≤exp (-s)) ∧
    ((r.label p).2=(r.label q).2 ↔ v (M.W p-M.W q)≤exp s) := by
  dsimp only
  unfold finiteRecord
  rw [record_label M v _ _ s p hp,record_label M v _ _ s q hq]
  exact ⟨cell_eq _ (ball_eq M v M.Z (-s)) _ _,cell_eq _ (ball_eq M v M.W s) _ _⟩

/-- A finite place has no inconsistent edges at any level away from their
finitely many exact threshold values. The proof uses the actual lifted
unit-distance equation in the original number field. -/
theorem finite_consistent (M : IncidencePiece K) (v : FinitePlace K) (s : ℝ)
    (e : Plane×Plane) (he : e∈M.E) (hn : s≠M.threshold v e) : (finiteRecord M v s).consistent e := by
  let n := M.threshold v e
  let a := v (M.Z e.1-M.Z e.2)
  let b := v (M.W e.1-M.W e.2)
  have ab : a*b=1 := by
    dsimp only [a,b]; rw [←map_mul,unit_model M he,map_one]
  have ha : 0<a := lt_of_le_of_ne (apply_nonneg v _) (by intro hz; simp [←hz] at ab)
  have binv : b=a⁻¹ := by field_simp; linarith only [ab]
  have ea : exp (-n)=a := by dsimp [n,threshold,a]; rw [neg_neg,exp_log ha]
  have eb : exp n=b := by change exp (-log a)=b; rw [exp_neg,exp_log ha,binv]
  obtain ⟨hp,hq⟩ := mem_product.mp (M.membership he)
  obtain ⟨z,w⟩ := finite_matches M v s _ _ (mem_union_left _ hp) (mem_union_right _ hq)
  have bit : (finiteRecord M v s).bit e=decide (s<n) := record_bit M v _ _ s e he
  unfold CoordinateLevel.consistent
  rw [bit]
  by_cases h : s<n
  · simp only [h,decide_true,ite_true]
    exact ⟨z.mpr (ea.symm.trans_le (exp_le_exp.mpr (neg_le_neg h.le))),
      fun hw => (not_le_of_gt ((exp_lt_exp.mpr h).trans_eq eb)) (w.mp hw)⟩
  · have h' := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hn)
    simp only [h,decide_false,ite_false]
    exact ⟨w.mpr (eb.symm.trans_le (exp_le_exp.mpr h'.le)),fun hz =>
      (not_le_of_gt ((exp_lt_exp.mpr (neg_lt_neg h')).trans_eq ea)) (z.mp hz)⟩

theorem finite_inconsistent_ae (M : IncidencePiece K) (v : FinitePlace K) :
    ∀ᵐs : ℝ,M.inconsistentMass (finiteRecord M v s)=0 := by
  have avoid : ∀ᵐs : ℝ,∀e : M.E,s≠M.threshold v e.val :=
    ae_all_iff.mpr fun e => volume.ae_ne _
  filter_upwards [avoid] with s hs
  have zero_event (A : Plane×Plane → Prop) (no : ∀e∈M.E,¬A e) : M.edgeProb A=0 := by
    have empty : M.E.filter A=∅ := eq_empty_iff_forall_notMem.mpr
      (fun e h => no e (mem_filter.mp h).1 (mem_filter.mp h).2)
    simp [edgeProb,empty]
  exact zero_event (fun e => ¬(finiteRecord M v s).consistent e)
    (fun e he => not_not_intro (finite_consistent M v s e he (hs ⟨e,he⟩)))

private lemma record_minority (M : IncidencePiece K) (he : 0<(M.E.card:ℝ)) (v : K → ℝ)
    (lab : ℝ → M.Vertices → M.Label×M.Label) (hl : Measurable lab) (s : ℝ) :
    M.minorityMass ((measurableRecord M v lab hl) s)=
      let h := M.edgeProb (fun e => s<M.threshold v e); min h (1-h) := by
  change M.minorityMass (realize M _) = _
  rw [raw_minority M _ he]
  have hh := edgeProb_congr M (fun e => ((measurableRecord M v lab hl) s).bit e=true) (fun e => s<M.threshold v e)
    (fun e he => by rw [record_bit M v lab hl s e he]; simp)
  exact congrArg (fun u : ℝ => min u (1-u)) hh


theorem arch_minority (M : IncidencePiece K) (he : 0<(M.E.card:ℝ)) (v : InfinitePlace K)
    (u w : ℝ×ℝ) (s : ℝ) : M.minorityMass (archRecord M v u w s)=
      let h := M.edgeProb (fun e => s<M.threshold v e); min h (1-h) :=
  record_minority M he v _ _ s

theorem finite_minority (M : IncidencePiece K) (he : 0<(M.E.card:ℝ)) (v : FinitePlace K)
    (s : ℝ) : M.minorityMass (finiteRecord M v s)=
      let h := M.edgeProb (fun e => s<M.threshold v e); min h (1-h) :=
  record_minority M he v _ _ s


end
end PlanarUnitDistances.Competition.IncidencePiece
