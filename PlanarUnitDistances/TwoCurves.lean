import PlanarUnitDistances.WeightedCurve

namespace PlanarUnitDistances.CurveRestriction
open Finset MvPolynomial
open scoped Classical
noncomputable section
variable {k P Q : Type*} [Field k] [Fintype P] [Fintype Q]

def reverseRow (N : P → Finset Q) (S : Finset P) (q : Q) : Finset P :=
  S.filter fun p => q ∈ N p

omit [Fintype P] in
private theorem reverse_count (N : P → Finset Q) (S : Finset P) :
    ∑ q, (reverseRow N S q).card = ∑ p ∈ S, (N p).card := by
  let rel (p : P) (q : Q) := q ∈ N p
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := S) (t := (univ : Finset Q)) rel
  have hrow (p : P) : univ.bipartiteAbove rel p=N p := by
    ext q
    simp [rel]
  rw [Finset.sum_congr rfl (fun p _ => congrArg Finset.card (hrow p))] at h
  exact h.symm

set_option maxHeartbeats 400000 in
/-- The manuscript's two irreducible plane curves actually retain the claimed
edges: the second application is on the first restricted graph with the
original point labels. Empty neighborhoods and repeated point labels are allowed. -/
theorem restrict_to_two_curves {n D : ℕ} (hn : 0<n) (hD : 0<D)
    (hp : Fintype.card P ≤ n) (hq : Fintype.card Q ≤ n)
    (x : P → Fin 2 → k) (y : Q → Fin 2 → k) (N : P → Finset Q)
    (dense : 16*n ≤ ∑ p, (N p).card)
    (thick : (16:ℝ)*n ≤ ((∑ p, (N p).card:ℕ):ℝ)^5/(512*D*(n:ℝ)^8))
    (left : ∀ a : Fin 4 ↪ Q, ∃ f : Poly k, f ≠ 0 ∧ f.totalDegree ≤ D ∧
      ∀ p ∈ common N a, eval (x p) f=0)
    (right : ∀ a : Fin 4 ↪ P, ∃ f : Poly k, f ≠ 0 ∧ f.totalDegree ≤ D ∧
      ∀ q ∈ common (reverseRow N univ) a, eval (y q) f=0) :
    ∃ f g : Poly k, Irreducible f ∧ f.totalDegree ≤ D ∧ Irreducible g ∧ g.totalDegree ≤ D ∧
      ((∑ p, (N p).card:ℕ):ℝ)^25 / ((512*(D:ℝ))^6*(n:ℝ)^48) ≤
      ∑ q ∈ univ.filter (fun q => eval (y q) g=0),
        ((reverseRow N (univ.filter (fun p => eval (x p) f=0)) q).card:ℝ) := by
  obtain ⟨f,hf,df,h₁⟩ := irreducible_curve_restriction hn hD hp hq x N dense left
  let S := univ.filter fun p => eval (x p) f=0
  let M := reverseRow N S
  have hsum : (∑ q, ((M q).card:ℝ)) = ∑ p ∈ S, ((N p).card:ℝ) := by
    exact_mod_cast reverse_count N S
  have hsum' : ((∑ q, (M q).card:ℕ):ℝ) = ∑ p ∈ S, ((N p).card:ℝ) := by
    push_cast
    exact hsum
  have dense' : 16*n ≤ ∑ q, (M q).card := by
    exact_mod_cast (thick.trans h₁ |>.trans_eq hsum'.symm)
  have right' (a : Fin 4 ↪ P) : ∃ g : Poly k, g≠0 ∧ g.totalDegree ≤ D ∧
      ∀ q ∈ common M a, eval (y q) g=0 := by
    obtain ⟨g,hg,dg,hz⟩ := right a
    refine ⟨g,hg,dg,fun q h => hz q ?_⟩
    apply mem_filter.mpr
    refine ⟨mem_univ _, fun i => ?_⟩
    have hi : a i ∈ M q := (Finset.mem_filter.mp h).2 i
    change a i ∈ Finset.filter (fun p => q ∈ N p) (univ : Finset P)
    exact Finset.mem_filter.mpr ⟨mem_univ _, (Finset.mem_filter.mp hi).2⟩
  obtain ⟨g,hg,dg,h₂⟩ := irreducible_curve_restriction hn hD hq hp y M dense' right'
  refine ⟨f,g,hf,df,hg,dg,?_⟩
  have hleft : 0 ≤ ((∑ p, (N p).card:ℕ):ℝ) := Nat.cast_nonneg _
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hDR : 0 < (D:ℝ) := Nat.cast_pos.mpr hD
  exact second_restriction (e₁ := ((∑ q, (M q).card:ℕ):ℝ)) hleft hnR hDR
    (h₁.trans_eq hsum'.symm) h₂

end
end PlanarUnitDistances.CurveRestriction
