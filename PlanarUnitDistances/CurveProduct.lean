import PlanarUnitDistances.PlaneBezout
import PlanarUnitDistances.ProductZeros

namespace PlanarUnitDistances.CurveProduct
open Finset MvPolynomial
open scoped Classical
noncomputable section
variable {k : Type*} [Field k] {s : ℕ}
abbrev Point (k : Type*) := Fin 2 → k
abbrev Curve (B : MvPolynomial (Fin 2) k) := {p : Point k // eval p B = 0}

/-- Substitution of affine-linear expressions cannot increase total degree. -/
theorem degree_after_linear_substitution {ι τ : Type*} (F : MvPolynomial ι k)
    (L : ι → MvPolynomial τ k) (hL : ∀ i, (L i).totalDegree ≤ 1) :
    (eval₂Hom C L F).totalDegree ≤ F.totalDegree := by
  classical
  conv_lhs => rw [F.as_sum,map_sum]
  apply totalDegree_finsetSum_le
  intro a ha
  rw [coe_eval₂Hom,eval₂_monomial]
  refine (totalDegree_mul ..).trans ?_
  simp only [totalDegree_C,zero_add]
  refine (totalDegree_finsetProd ..).trans ((sum_le_sum ?_).trans (le_totalDegree ha))
  intro j _
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (a j) (hL j))

def coords (x : Fin s → Point k) (b : Fin s × Fin 2) : k := x b.1 b.2

private def axis (x : Fin s → Point k) (i : Fin s) (b : Fin s × Fin 2) :
    MvPolynomial (Fin 2) k := if b.1 = i then X b.2 else C (x b.1 b.2)

private lemma slice_eval (x : Fin s → Point k) (i : Fin s) (t : Point k)
    (F : MvPolynomial (Fin s × Fin 2) k) :
    eval t (eval₂Hom C (axis x i) F) = eval (coords (Function.update x i t)) F := by
  change eval t (eval₂ C (axis x i) F) = eval _ F
  rw [eval₂_comp_left]
  congr 1
  · ext a
    simp
  · funext b
    by_cases h : b.1 = i <;> simp [axis,coords,h,Function.update]

/-- Manuscript product-of-curves zero count, with actual irreducible plane equations
and an actual ambient polynomial. A witness on the product may lie outside the samples. -/
theorem zeros_on_product (B : Fin s → MvPolynomial (Fin 2) k)
    (hB : ∀ i, Irreducible (B i)) (F : MvPolynomial (Fin s × Fin 2) k)
    (D E n : ℕ) (hD : ∀ i, (B i).totalDegree ≤ D) (hE : F.totalDegree ≤ E)
    (S : ∀ i, Finset (Curve (B i))) (size : ∀ i, (S i).card ≤ n)
    (w : ∀ i, Curve (B i)) (hw : eval (coords fun i => (w i).val) F ≠ 0) :
    ((Fintype.piFinset S).filter fun x => eval (coords fun i => (x i).val) F = 0).card ≤
      s * D * E * n^(s-1) := by
  classical
  refine ProductZeros.curve_product_bound (fun i => Curve (B i)) S
    (fun x => eval (coords fun i => (x i).val) F) D E n size ?_ w hw
  intro x i hx
  let v : Fin s → Point k := fun j => (x j).val
  let G := eval₂Hom C (axis v i) F
  have eg (t : Curve (B i)) : eval t.val G =
      eval (coords fun j => ((Function.update x i t) j).val) F := by
    rw [show eval t.val G = eval (coords (Function.update v i t.val)) F from slice_eval ..]
    congr 2
    funext ⟨j,b⟩
    by_cases h : j=i
    · subst j; simp [coords]
    · simp [coords,v,h]
  have hnd : ¬ B i ∣ G := by
    rintro ⟨H,hH⟩
    have hz : eval (x i).val G = 0 := by rw [hH,map_mul,(x i).prop,zero_mul]
    rw [eg,Function.update_eq_self] at hz
    exact hx hz
  let A := (S i).filter fun t => eval (coords fun j => ((Function.update x i t) j).val) F = 0
  let emb : Curve (B i) ↪ Point k := ⟨Subtype.val,Subtype.val_injective⟩
  have count := PlaneBezout.common_zeros (B i) G (hB i) hnd (A.map emb)
    (by intro t ht; obtain ⟨y,_,rfl⟩ := mem_map.mp ht; exact y.prop)
    (by intro t ht; obtain ⟨y,hy,rfl⟩ := mem_map.mp ht; exact (eg y).trans (mem_filter.mp hy).2)
  have deg : G.totalDegree ≤ E := (degree_after_linear_substitution F (axis v i)
    (fun b => by unfold axis; split <;> simp)).trans hE
  exact (by simpa only [card_map] using count : A.card ≤ _).trans (Nat.mul_le_mul (hD i) deg)

end
end PlanarUnitDistances.CurveProduct
