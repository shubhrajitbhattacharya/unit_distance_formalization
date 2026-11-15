import PlanarUnitDistances.Main
import PlanarUnitDistances.GridLocus

/-! The product-of-curves obstruction with a single finite exceptional degree
uniform over all pairs of curves of degree at most 80. -/

noncomputable section

namespace PlanarUnitDistances.CurveRestriction

/-- For an arbitrary exceptional degree the obstruction is effective once
the explicit growth condition holds. The exponent left after division is 3/5. -/
theorem incompatible_counts_of_degree {n e₂ m m' H : ℝ} (E : ℕ)
    (hn0 : 0 < n)
    (growth : 12 * curveDegree * (E:ℝ) * restrictionCost^32 < n^(3/5:ℝ))
    (_he : 0 < e₂) (hm : 0 < m) (hm' : 0 < m')
    (hmn : m ≤ n) (hmn' : m' ≤ n)
    (dense : n ^ (2 - 25/2000 : ℝ) / restrictionCost ≤ e₂)
    (grids : e₂^32 / (m^24 * m'^28) ≤ H)
    (zeros : H ≤ 12 * curveDegree * (E:ℝ) * n^11) : False := by
  have hk : 0 < restrictionCost := by unfold restrictionCost curveDegree; positivity
  have hd : 0 < curveDegree := by norm_num [curveDegree]
  have hden : 0 < m^24 * m'^28 := by positivity
  have hlo := pow_le_pow_left₀ (by positivity) dense 32
  rw [div_pow] at hlo
  have hup : e₂^32 ≤ (12 * curveDegree * (E:ℝ) * n^11) * (m^24 * m'^28) :=
    (div_le_iff₀ hden).mp (grids.trans zeros)
  have hbound : n ^ ((2 - 25/2000:ℝ)*32) ≤
      12 * curveDegree * (E:ℝ) * restrictionCost^32 * n^63 := by
    rw [Real.rpow_mul hn0.le]
    rw [Real.rpow_ofNat]
    calc
      _ ≤ e₂^32 * restrictionCost^32 := (div_le_iff₀ (by positivity)).mp hlo
      _ ≤ ((12 * curveDegree * (E:ℝ) * n^11) * (n^24 * n^28)) *
          restrictionCost^32 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact hup.trans (by gcongr)
      _ = _ := by ring
  have hsmall : n ^ (3/5:ℝ) ≤ 12 * curveDegree * (E:ℝ) * restrictionCost^32 := by
    apply (mul_le_mul_iff_left₀ (by positivity : 0 < n^63)).mp
    calc
      n ^ (3/5:ℝ) * n^63 = n ^ ((2 - 25/2000:ℝ)*32) := by
        rw [← Real.rpow_natCast n 63, ← Real.rpow_add hn0]
        congr 1
        norm_num
      _ ≤ _ := hbound
  exact (not_lt_of_ge hsmall) growth

end PlanarUnitDistances.CurveRestriction

namespace PlanarUnitDistances.GridObstruction
open MvPolynomial Finset CurveProduct
open scoped Classical
variable {k : Type*} [Field k]

private theorem lower_normalization (e m l : ℝ) (hm : 0 < m) (hl : 0 < l) :
    e^32/(m^24*l^28) = m^8*l^4*(e/(m*l))^32 := by
  field_simp

/-- A dense actual graph on two curves cannot have all its complete grids in
the specified bounded-degree exceptional locus. The nonzero evaluation may
be anywhere on the product of the curves. -/
theorem no_dense_grid_locus_of_degree (f g : Eqn k) (hf : Irreducible f) (hg : Irreducible g)
    (A B : Finset (Pt k)) [Nonempty A] [Nonempty B]
    (hA : ∀ x∈A, eval x f=0) (hB : ∀ x∈B, eval x g=0)
    (edge : A → B → Prop) [DecidableRel edge] (n : ℕ)
    (E : ℕ) (hn0 : (0:ℝ) < n)
    (growth : 12*CurveRestriction.curveDegree*(E:ℝ)*CurveRestriction.restrictionCost^32 < (n:ℝ)^(3/5:ℝ))
    (df : f.totalDegree ≤ 80) (dg : g.totalDegree ≤ 80)
    (an : A.card ≤ n) (bn : B.card ≤ n)
    (dense : (n:ℝ)^(2-25/2000:ℝ)/CurveRestriction.restrictionCost ≤
      ((univ.filter fun z : A × B => edge z.1 z.2).card : ℝ))
    (F : MvPolynomial (Fin 12 × Fin 2) k) (hF : F.totalDegree ≤ E)
    (w : ∀ i, Curve (curveAt f g i)) (hw : eval (coords (fun i => (w i).val)) F≠0)
    (vanish : ∀ (p : Fin 8 → A) (r : Fin 4 → B), (∀ i j, edge (p i) (r j)) →
      eval (coords (positions (fun i => (p i).val) (fun j => (r j).val))) F=0) : False := by
  let e : ℝ := (univ.filter fun z : A × B => edge z.1 z.2).card
  have hm : (0:ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hl : (0:ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hc : 0 < CurveRestriction.restrictionCost := by
    norm_num [CurveRestriction.restrictionCost,CurveRestriction.curveDegree]
  have he : 0 < e := lt_of_lt_of_le (by positivity) dense
  have lo := GridCount.complete_grid_count edge 8 4
  have hi := polynomial_grid_upper f g hf hg A B hA hB edge 80 E n
    df dg an bn F hF w hw vanish
  apply CurveRestriction.incompatible_counts_of_degree (H := ((upper_grids A B edge).card : ℝ)) E hn0 growth he hm hl
      (by simpa using (show (A.card:ℝ) ≤ n by exact_mod_cast an))
      (by simpa using (show (B.card:ℝ) ≤ n by exact_mod_cast bn)) dense
  · rw [lower_normalization _ _ _ hm hl]
    exact lo
  · simpa only [CurveRestriction.curveDegree,
      Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
      (show ((upper_grids A B edge).card:ℝ) ≤ ((12*80*E*n^11 : ℕ):ℝ)
        by exact_mod_cast hi)

end PlanarUnitDistances.GridObstruction

namespace PlanarUnitDistances.GridLocus
open MvPolynomial Finset CurveReflection
open scoped Classical

/-- A single bound for every eligible pair, including the existence of a
nonzero evaluation on the actual twelve-fold product. -/
def BoundsDegree (E : ℕ) : Prop := ∀ f g, curvePair f g →
  f.totalDegree ≤ 80 → g.totalDegree ≤ 80 →
  ∃ F, F.totalDegree ≤ E ∧ separates f g F

def UniformExceptionalDegree : Prop := ∃ E : ℕ, BoundsDegree E


private def idx : ((Fin 8 ⊕ Fin 4) × Fin 2) → (Fin 12 × Fin 2) :=
  fun e => (finSumFinEquiv e.1,e.2)

private theorem reindex_eval (F : TuplePoly) (p : Fin 8 → Point) (r : Fin 4 → Point) :
    eval (CurveProduct.coords (GridObstruction.positions p r)) (rename idx F)=
      eval (fun e => join p r e.1 e.2) F := by
  rw [eval_rename]
  apply congrArg (fun t => eval t F)
  funext e
  obtain ⟨(i|j),k⟩ := e
  · change Fin.append p r (Fin.castAdd 4 i) k=p i k
    rw [Fin.append_left]
  · change Fin.append p r (Fin.natAdd 8 j) k=r j k
    rw [Fin.append_right]

/-- Once compatibility of complete grids and the effective exceptional equation
are available, one obtains a contradiction on the actual restricted bipartite graph. -/
theorem excludes_dense_graph_of_degree (E : ℕ) (eff : BoundsDegree E) (f g : PlanePoly) (pair : curvePair f g)
    (df : f.totalDegree ≤ 80) (dg : g.totalDegree ≤ 80)
    (A B : Finset Point) [Nonempty A] [Nonempty B]
    (hA : ∀ x∈A, eval x f=0) (hB : ∀ x∈B, eval x g=0)
    (edge : A → B → Prop) [DecidableRel edge] (n : ℕ)
    (hn : (0:ℝ) < n)
    (growth : 12*CurveRestriction.curveDegree*(E:ℝ)*CurveRestriction.restrictionCost^32 < (n:ℝ)^(3/5:ℝ)) (an : A.card ≤ n) (bn : B.card ≤ n)
    (dense : (n:ℝ)^(2-25/2000:ℝ)/CurveRestriction.restrictionCost ≤
      ((Finset.univ.filter fun z : A × B => edge z.1 z.2).card : ℝ))
    (comp : ∀ (p : Fin 8 → A) (r : Fin 4 → B), (∀ i j, edge (p i) (r j)) →
      compatibleTuple (join (fun i => (p i).val) (fun j => (r j).val))) : False := by
  obtain ⟨F,hF,hvan,w,hw,hw'⟩ := eff f g pair df dg
  let l (i : Fin 8) := w (.inl i)
  let r (i : Fin 4) := w (.inr i)
  let pos := GridObstruction.positions l r
  have on (i : Fin 12) : eval (pos i) (GridObstruction.curveAt f g i)=0 := by
    refine Fin.addCases (m:=8) (n:=4) ?_ ?_ i
    · intro j; simpa [pos,GridObstruction.positions,GridObstruction.curveAt,l] using hw.1 j
    · intro j; simpa [pos,GridObstruction.positions,GridObstruction.curveAt,r] using hw.2 j
  apply GridObstruction.no_dense_grid_locus_of_degree f g (pair.1 f (by simp)).1 (pair.1 g (by simp)).1
    A B hA hB edge n E hn growth df dg an bn dense (rename idx F)
    ((totalDegree_rename_le _ _).trans hF) (fun i => ⟨pos i,on i⟩)
  · change eval (CurveProduct.coords (GridObstruction.positions l r)) _ ≠ 0
    rw [reindex_eval]
    have eqw : join l r=w := by funext s; cases s <;> rfl
    rwa [eqw]
  · intro p r' complete
    rw [reindex_eval]
    apply hvan _ _ (comp p r' complete)
    exact ⟨fun i => hA _ (p i).prop,fun j => hB _ (r' j).prop⟩


/-- Pull the complex position-locus contradiction back along the actual real
embedding p ↦ (x+iy,x−iy), without identifying ordered rectangles or removing
repeated vertices. The edge count is literally the restricted original count. -/
theorem excludes_dense_real_graph_of_degree (E : ℕ) (eff : BoundsDegree E) (f g : PlanePoly) (pair : curvePair f g)
    (df : f.totalDegree ≤ 80) (dg : g.totalDegree ≤ 80)
    (A B : Finset OAI.PlanarUnitDistances.Plane) (ha : A.Nonempty) (hb : B.Nonempty)
    (hA : ∀ x∈A, eval (realPoint x) f=0) (hB : ∀ x∈B, eval (realPoint x) g=0)
    (edges : planeEdges) (n : ℕ) (hn : (0:ℝ) < n)
    (growth : 12*CurveRestriction.curveDegree*(E:ℝ)*CurveRestriction.restrictionCost^32 < (n:ℝ)^(3/5:ℝ)) (an : A.card ≤ n) (bn : B.card ≤ n)
    (dense : (n:ℝ)^(2-25/2000:ℝ)/CurveRestriction.restrictionCost ≤
      (((A ×ˢ B).filter (fun z => z∈edges)).card : ℝ))
    (comp : ∀ (p : Fin 8 → OAI.PlanarUnitDistances.Plane) (r : Fin 4 → OAI.PlanarUnitDistances.Plane),
      (∀ i j, (p i,r j)∈edges) → compatibleTuple (join (realPoint ∘ p) (realPoint ∘ r))) : False := by
  classical
  let A' := A.map realPoint
  let B' := B.map realPoint
  let eA := Finset.equivMap realPoint A
  let eB := Finset.equivMap realPoint B
  let edge (p : A') (r : B') := ((eA.symm p).val,(eB.symm r).val)∈edges
  have cardEq : (univ.filter (fun z : A' × B' => edge z.1 z.2)).card =
      ((A ×ˢ B).filter (fun z => z∈edges)).card := by
    apply Finset.card_bij (fun z _ => ((eA.symm z.1).val,(eB.symm z.2).val))
    · intro z hz
      exact mem_filter.mpr ⟨mem_product.mpr ⟨(eA.symm _).prop,(eB.symm _).prop⟩,(mem_filter.mp hz).2⟩
    · intro x _ y _ h
      exact Prod.ext (eA.symm.injective (Subtype.ext (congrArg Prod.fst h)))
        (eB.symm.injective (Subtype.ext (congrArg Prod.snd h)))
    · intro z hz
      obtain ⟨hz0,hzE⟩ := mem_filter.mp hz
      obtain ⟨hp,hq⟩ := mem_product.mp hz0
      refine ⟨(eA ⟨z.1,hp⟩,eB ⟨z.2,hq⟩),?_,?_⟩
      · simpa [edge] using hzE
      · simp
  let : Nonempty A' := (show A'.Nonempty from ha.map).coe_sort
  let : Nonempty B' := (show B'.Nonempty from hb.map).coe_sort
  have onA (p : Point) (hp : p ∈ A') : eval p f=0 := by
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hp
    exact hA x hx
  have onB (q : Point) (hq : q ∈ B') : eval q g=0 := by
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hq
    exact hB x hx
  apply excludes_dense_graph_of_degree E eff f g pair df dg A' B' onA onB edge n hn growth
    (by simpa [A'] using an) (by simpa [B'] using bn) (by rwa [cardEq])
  · intro p r E
    have h := comp (fun i => (eA.symm (p i)).val) (fun j => (eB.symm (r j)).val) E
    have eqA (x : A') : realPoint (eA.symm x).val=x.val := congrArg Subtype.val (eA.apply_symm_apply x)
    have eqB (x : B') : realPoint (eB.symm x).val=x.val := congrArg Subtype.val (eB.apply_symm_apply x)
    simpa only [Function.comp_def,eqA,eqB] using h

end PlanarUnitDistances.GridLocus
end
