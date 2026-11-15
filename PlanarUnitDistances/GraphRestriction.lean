import PlanarUnitDistances.TwoCurves
import PlanarUnitDistances.CurveReflection
import PlanarUnitDistances.Main
import PlanarUnitDistances.GridLocus

/-! The finite two-curve restriction at the threshold of the organized graph theorem. -/
noncomputable section

namespace PlanarUnitDistances.GraphRestriction
open Finset MvPolynomial CurveRestriction CurveReflection
open OAI.PlanarUnitDistances
open scoped Classical ComplexConjugate

private theorem threshold {n u : ℝ} (hn : (2:ℝ)^10000 ≤ n) (hu : 1/16 ≤ u) :
    (2:ℝ)^100 ≤ n^u := by
  have h₁ : 1 ≤ n := le_trans (one_le_pow₀ (by norm_num)) hn
  calc
    (2:ℝ)^100 ≤ 2^625 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    _ = ((2:ℝ)^10000)^(1/16:ℝ) := by
      rw [← Real.rpow_natCast (2:ℝ) 10000, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    _ ≤ n^(1/16:ℝ) := Real.rpow_le_rpow (by positivity) hn (by norm_num)
    _ ≤ n^u := Real.rpow_le_rpow_of_exponent_le h₁ hu

/-- Both density prerequisites of the two successive curve restrictions. -/
theorem prerequisites {n e : ℝ} (hn : (2:ℝ)^10000 ≤ n) (he : n^(2-1/2000:ℝ) ≤ e) :
    16*n ≤ e ∧ 16*n ≤ e^5 / (512*80*n^8) := by
  have hn₀ : 0 < n := lt_of_lt_of_le (by positivity) hn
  constructor
  · calc
      16*n ≤ n^(1-1/2000:ℝ)*n := by
        gcongr; exact (by norm_num : (16:ℝ) ≤ 2^100).trans (threshold hn (by norm_num))
      _ = n^(2-1/2000:ℝ) := by
        conv_lhs => enter [2]; rw [← Real.rpow_one n]
        rw [← Real.rpow_add hn₀]; norm_num
      _ ≤ e := he
  · apply (le_div_iff₀ (by positivity)).mpr
    calc
      16*n*(512*80*n^8) = (16*512*80)*n^9 := by ring
      _ ≤ n^((2-1/2000:ℝ)*5-9)*n^9 := by
        gcongr; exact (by norm_num : (16*512*80:ℝ) ≤ 2^100).trans (threshold hn (by norm_num))
      _ = (n^(2-1/2000:ℝ))^5 := by
        rw [← Real.rpow_natCast n 9, ← Real.rpow_add hn₀,
          show ((2-1/2000:ℝ)*5-9+((9:ℕ):ℝ))=(2-1/2000)*5 by norm_num,
          Real.rpow_mul hn₀.le, Real.rpow_ofNat]
      _ ≤ e^5 := pow_le_pow_left₀ (by positivity) he _

/-- The lower bound left after both curve restrictions at the original graph exponent. -/
theorem density_after_restriction {n e : ℝ} (hn : 0<n) (he : n^(2-1/2000:ℝ) ≤ e) :
    n^(2-25/2000:ℝ)/restrictionCost ≤ e^25/((512*80)^6*n^48) := by
  have hk : 0 < restrictionCost := by norm_num [restrictionCost, curveDegree]
  apply (div_le_div_iff₀ hk (by positivity)).mpr
  calc
    n^(2-25/2000:ℝ)*((512*80)^6*n^48) = n^((2-1/2000:ℝ)*25)*restrictionCost := by
      rw [mul_comm ((512*80:ℝ)^6), ← mul_assoc, ← Real.rpow_natCast n 48,
        ← Real.rpow_add hn]
      norm_num [restrictionCost,curveDegree]
    _ = (n^(2-1/2000:ℝ))^25*restrictionCost := by rw [Real.rpow_mul hn.le, Real.rpow_ofNat]
    _ ≤ e^25*restrictionCost := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) he _) hk.le

/-- Both point thresholds hold at the same retained density and the original n. -/
theorem retained_threshold {n e₂ : ℝ} (hn : (2:ℝ)^10000 ≤ n)
    (dense : n^(2-25/2000:ℝ)/restrictionCost ≤ e₂) :
    (80:ℝ)^2 < n^(9/10:ℝ) ∧ n^(9/10:ℝ) ≤ e₂/n := by
  have hn₀ : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hk : 0 < restrictionCost := by norm_num [restrictionCost,curveDegree]
  refine ⟨(by norm_num : (80:ℝ)^2 < 2^100).trans_le (threshold hn (by norm_num)), ?_⟩
  apply (le_div_iff₀ hn₀).mpr
  apply le_trans _ dense
  apply (le_div_iff₀ hk).mpr
  have hcost : restrictionCost ≤ n^(1/10-25/2000:ℝ) :=
    (by norm_num [restrictionCost,curveDegree] : restrictionCost ≤ (2:ℝ)^100).trans
      (threshold hn (by norm_num))
  calc
    n^(9/10:ℝ)*n*restrictionCost ≤ n^(9/10:ℝ)*n*n^(1/10-25/2000:ℝ) := by gcongr
    _ = n^(2-25/2000:ℝ) := by
      conv_lhs => enter [1,2]; rw [← Real.rpow_one n]
      rw [← Real.rpow_add hn₀, ← Real.rpow_add hn₀]; norm_num


variable {n : ℕ} {K : Type} [Field K] [NumberField K]

/-- Original vertices in each row, including precisely the original directed edges. -/
def rows (G : AdmissibleGraph n K) (p : G.points) : Finset G.points :=
  univ.filter fun q => (p.val,q.val) ∈ G.edges

/-- The four-anchor vanishing assertions needed on the two sides, in null coordinates. -/
def CurvesForRows (G : AdmissibleGraph n K) : Prop :=
  (∀ a : Fin 4 ↪ G.points, ∃ f : CurveReflection.Poly, f ≠ 0 ∧ f.totalDegree ≤ 80 ∧
    ∀ p ∈ common (rows G) a, eval (realPoint p.val) f = 0) ∧
  (∀ a : Fin 4 ↪ G.points, ∃ f : CurveReflection.Poly, f ≠ 0 ∧ f.totalDegree ≤ 80 ∧
    ∀ q ∈ common (reverseRow (rows G) univ) a, eval (realPoint q.val) f = 0)

/-- Literal edges in the original graph with endpoints in the two selected sets. -/
def edgesOn (G : AdmissibleGraph n K) (A B : Finset Plane) : Finset (Plane × Plane) :=
  (A ×ˢ B).filter fun e => e ∈ G.edges

private def toPoints (G : AdmissibleGraph n K) (S : Finset G.points) : Finset Plane :=
  S.map (Function.Embedding.subtype _)

private theorem all_points (G : AdmissibleGraph n K) : toPoints G univ = G.points := by
  ext p
  simp [toPoints]

private theorem all_edges (G : AdmissibleGraph n K) : edgesOn G G.points G.points = G.edges := by
  ext e
  exact (mem_filter.trans <| and_iff_right_of_imp (fun h =>
    mem_product.mpr (G.endpoints e h)))

private theorem edgesOn_count (G : AdmissibleGraph n K) (S T : Finset G.points) :
    (edgesOn G (toPoints G S) (toPoints G T)).card =
      ∑ q ∈ T, (reverseRow (rows G) S q).card := by
  simp only [edgesOn, Finset.card_filter, Finset.sum_product_right, toPoints, Finset.sum_map,
    Function.Embedding.coe_subtype, reverseRow, rows, Finset.mem_filter, Finset.mem_univ, true_and]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro p _
  by_cases h : (p.val,q.val) ∈ G.edges <;> simp [h]

theorem rows_count (G : AdmissibleGraph n K) :
    ∑ p, (rows G p).card = G.edges.card := by
  have hc := edgesOn_count G univ univ
  simp only [all_points, all_edges] at hc
  rw [hc]
  let rel (p q : G.points) := (p.val,q.val) ∈ G.edges
  have eq := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (univ : Finset G.points)) (t := univ) rel
  simpa [bipartiteAbove, bipartiteBelow, rel, rows, reverseRow] using eq

/-- A curve contains these many original real vertices, is invariant under
conjugation, and has two witnesses distinguishing both null-coordinate projections. -/
structure RichSide (A : Finset Plane) (f : CurveReflection.Poly) : Prop where
  irred : Irreducible f
  degree : f.totalDegree ≤ 80
  vanishes : ∀ p ∈ A, eval (realPoint p) f = 0
  many : 80^2 < A.card
  scalar : ∃ c : ℂ, c ≠ 0 ∧ reflect f = C c * f
  symmetry : ∀ x : CurveReflection.Point, eval (reflectPoint x) f=0 ↔ eval x f=0
  equal_degrees : f.degreeOf 0 = f.degreeOf 1
  projections : ∃ p ∈ A, ∃ q ∈ A, ∀ j : Fin 2, realPoint p j ≠ realPoint q j

private theorem rich_side (A : Finset Plane) (f : CurveReflection.Poly)
    (irred : Irreducible f) (degree : f.totalDegree ≤ 80)
    (hz : ∀ p ∈ A, eval (realPoint p) f = 0) (many : 80^2 < A.card) : RichSide A f := by
  obtain ⟨h₁,h₂,h₃⟩ := rich_curve_symmetry f irred degree A many hz
  obtain ⟨p,hp,q,hq,_,_,hpq⟩ := rich_curve_nonconstant_projections f irred degree A many hz
  exact ⟨irred,degree,hz,many,h₁,h₂,h₃,p,hp,q,hq,hpq⟩

/-- Data on the same two retained curves in the original directed graph. -/
structure Restricted (G : AdmissibleGraph n K) where
  A : Finset Plane
  B : Finset Plane
  f : CurveReflection.Poly
  g : CurveReflection.Poly
  left_subset : A ⊆ G.points
  right_subset : B ⊆ G.points
  left : RichSide A f
  right : RichSide B g
  dense : (n:ℝ)^(2-25/2000:ℝ)/restrictionCost ≤ ((edgesOn G A B).card:ℝ)
  left_count : ((edgesOn G A B).card:ℝ) / n ≤ A.card
  right_count : ((edgesOn G A B).card:ℝ) / n ≤ B.card
  circle_count : (n:ℝ)^(9/10:ℝ) ≤ ((edgesOn G A B).card:ℝ) / n
  no_common_circle : ¬ ∃ c : Plane,
    (∀ p ∈ A, dist p c = 1) ∧ (∀ q ∈ B, dist q c = 1)

private theorem toPoints_subset (G : AdmissibleGraph n K) (S : Finset G.points) :
    toPoints G S ⊆ G.points := by
  intro p h
  obtain ⟨q,_,rfl⟩ := mem_map.mp h
  exact q.prop

/-- Assuming only the common-neighbor curves, the exact counterexample density
retains the asserted number of original edges on two rich symmetric curves.
The same vertex samples exclude a common Euclidean unit circle. -/
theorem retain (G : AdmissibleGraph n K) (hn : 2^10000 ≤ n)
    (dense : (n:ℝ)^(2-1/2000:ℝ) ≤ G.edges.card) (localCurves : CurvesForRows G) :
    Nonempty (Restricted G) := by
  have hnR : (2:ℝ)^10000 ≤ n := by exact_mod_cast hn
  have hn₀ : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hnPos : 0 < (n:ℝ) := by exact_mod_cast hn₀
  have hd := prerequisites hnR dense
  have hcard : Fintype.card G.points ≤ n := by simpa using G.point_bound
  have hed : 16*n ≤ ∑ p, (rows G p).card := by rw [rows_count]; exact_mod_cast hd.1
  have hthick : (16:ℝ)*n ≤ ((∑ p, (rows G p).card : ℕ):ℝ)^5/(512*(80:ℝ)*n^8) := by
    rw [rows_count]; exact hd.2
  obtain ⟨f,g,hf,df,hg,dg,hE⟩ := restrict_to_two_curves hn₀ (by decide : 0<80)
    hcard hcard (fun p => realPoint p.val) (fun q => realPoint q.val) (rows G)
    hed hthick localCurves.1 localCurves.2
  let S := univ.filter fun p : G.points => eval (realPoint p.val) f = 0
  let T := univ.filter fun q : G.points => eval (realPoint q.val) g = 0
  let A := toPoints G S
  let B := toPoints G T
  let E := edgesOn G A B
  have den : (n:ℝ)^(2-25/2000:ℝ)/restrictionCost ≤ (E.card:ℝ) := by
    have hc : (E.card:ℝ) = ∑ q ∈ T, ((reverseRow (rows G) S q).card:ℝ) := by
      exact_mod_cast edgesOn_count G S T
    rw [hc]
    apply (density_after_restriction hnPos dense).trans
    rw [rows_count] at hE
    exact hE
  have hA : A ⊆ G.points := toPoints_subset G S
  have hB : B ⊆ G.points := toPoints_subset G T
  have hsize := card_le_card (filter_subset (fun e : Plane × Plane => e ∈ G.edges) (A×ˢB))
  rw [card_product] at hsize
  have eab : E.card ≤ A.card * B.card := hsize
  have hleft : (E.card:ℝ) / n ≤ A.card := by
    apply (div_le_iff₀ hnPos).mpr
    exact_mod_cast eab.trans (Nat.mul_le_mul_left _ ((card_le_card hB).trans G.point_bound))
  have hright : (E.card:ℝ) / n ≤ B.card := by
    apply (div_le_iff₀ hnPos).mpr
    rw [mul_comm]
    exact_mod_cast eab.trans (Nat.mul_le_mul_right _ ((card_le_card hA).trans G.point_bound))
  obtain ⟨hdegree,hcircle⟩ := retained_threshold hnR den
  have manyA : 80^2 < A.card := by exact_mod_cast hdegree.trans_le (hcircle.trans hleft)
  have manyB : 80^2 < B.card := by exact_mod_cast hdegree.trans_le (hcircle.trans hright)
  have onA (p : Plane) (hp : p ∈ A) : eval (realPoint p) f = 0 := by
    obtain ⟨q,hq,rfl⟩ := mem_map.mp hp
    exact (mem_filter.mp hq).2
  have onB (p : Plane) (hp : p ∈ B) : eval (realPoint p) g = 0 := by
    obtain ⟨q,hq,rfl⟩ := mem_map.mp hp
    exact (mem_filter.mp hq).2
  refine ⟨⟨A,B,f,g,hA,hB,rich_side A f hf df onA manyA,rich_side B g hg dg onB manyB,
    den,hleft,hright,hcircle,?_⟩⟩
  rintro ⟨c,ac,bc⟩
  have hpos : 0 < (E.card:ℝ) := lt_of_lt_of_le (by
    exact div_pos (Real.rpow_pos_of_pos hnPos _) (by norm_num [restrictionCost,curveDegree])) den
  obtain ⟨e,he⟩ := card_pos.mp (show 0 < E.card by exact_mod_cast hpos)
  obtain ⟨hab,hG⟩ := mem_filter.mp he
  obtain ⟨ha,hb⟩ := mem_product.mp hab
  have hlt := G.circle e.1 e.2 hG c (ac _ ha) (bc _ hb)
  have hsub : A ⊆ G.points.filter (fun p => dist p c = 1) := fun p hp => mem_filter.mpr ⟨hA hp,ac p hp⟩
  exact (not_le_of_gt hlt) ((hcircle.trans hleft).trans (by exact_mod_cast card_le_card hsub))


/-- The precise pair-of-curves hypothesis for the exceptional grid theorem. -/
theorem Restricted.curve_pair {G : AdmissibleGraph n K} (R : Restricted G) :
    GridLocus.curvePair R.f R.g := by
  constructor
  · have side (f : CurveReflection.Poly) (A : Finset Plane) (d : RichSide A f) :
        Irreducible f ∧ (∀ p, eval p f = 0 ↔ eval (reflectPoint p) f = 0) ∧
          ∀ j : Fin 2, ∃ p q : CurveReflection.Point, eval p f=0 ∧ eval q f=0 ∧ p j ≠ q j := by
      refine ⟨d.irred,fun p => (d.symmetry p).symm,?_⟩
      obtain ⟨p,hp,q,hq,h⟩ := d.projections
      exact fun j => ⟨_,_,d.vanishes p hp,d.vanishes q hq,h j⟩
    intro f hf
    simp only [mem_insert,mem_singleton] at hf
    rcases hf with rfl|rfl
    · exact side _ _ R.left
    · exact side _ _ R.right
  · rintro ⟨c,eq⟩
    obtain ⟨v,_,hv⟩ := hyperbola_one_is_unit_circle c (conj c) (fun z w h => by
      simpa [mul_comm] using congrArg conj h)
    apply R.no_common_circle
    exact ⟨v,fun p hp => (hv p).mp ((eq (realPoint p)).1.mp (R.left.vanishes p hp)),
      fun q hq => (hv q).mp ((eq (realPoint q)).2.mp (R.right.vanishes q hq))⟩

end PlanarUnitDistances.GraphRestriction
