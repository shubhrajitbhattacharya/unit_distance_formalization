import Mathlib

/-! A distinct-point affine Bézout inequality in two variables.
The proof uses bounded-degree polynomial spaces and finite interpolation. -/

namespace PlanarUnitDistances.PlaneBezout
open MvPolynomial Finset Module
open scoped BigOperators Classical
noncomputable section
variable (k : Type*) [Field k]
abbrev Poly := MvPolynomial (Fin 2) k
abbrev V (n : ℕ) := restrictTotalDegree (Fin 2) k n

private def triangle (n : ℕ) := {p : Fin 2 →₀ ℕ // p.sum (fun _ a => a) ≤ n}

private lemma triangle_sum (p : Fin 2 →₀ ℕ) : p.sum (fun _ a => a) = p 0+p 1 := by
  rw [Finsupp.sum_fintype]
  simp [Fin.sum_univ_two]
  all_goals simp

private def triangleEquiv (n : ℕ) : triangle n ≃ (i : Fin (n+1)) × Fin (i.val+1) where
  toFun p := ⟨⟨p.1 0+p.1 1, by have h := p.2; rw [triangle_sum] at h; omega⟩,
    ⟨p.1 0,by change p.1 0 < p.1 0+p.1 1+1; omega⟩⟩
  invFun x := ⟨Finsupp.equivFunOnFinite.symm ![x.2.val,x.1.val-x.2.val], by
    rw [triangle_sum]; simp; omega⟩
  left_inv p := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp
  right_inv x := by
    rcases x with ⟨⟨i,hi⟩,⟨j,hj⟩⟩
    simp
    grind

theorem degree_space_dimension (n : ℕ) :
    2*finrank k (V k n) = (n+1)*(n+2) := by
  letI : Fintype (triangle n) := Fintype.ofEquiv _ (triangleEquiv n).symm
  let B : Module.Basis (triangle n) k (V k n) := basisRestrictSupport k _
  rw [Module.finrank_eq_card_basis B, Fintype.card_congr (triangleEquiv n), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [sum_add_distrib]
  have h := sum_range_id_mul_two (n+1)
  simp at h ⊢
  rw [Fin.sum_univ_eq_sum_range (fun i => i)]
  nlinarith only [h]

variable {k}
private def times (F : Poly k) (n m : ℕ) (h : F.totalDegree + n ≤ m) : V k n →ₗ[k] V k m where
  toFun x := ⟨F*x.1, (mem_restrictTotalDegree _ _ _).mpr
    ((totalDegree_mul ..).trans (by have := (mem_restrictTotalDegree _ _ _).mp x.2; omega))⟩
  map_add' x y := by ext1; exact mul_add .. 
  map_smul' r x := by ext1; exact mul_smul_comm .. 

private def evaluate (S : Finset (Fin 2 → k)) (n : ℕ) : V k n →ₗ[k] (S → k) where
  toFun f x := MvPolynomial.eval x.val f.val
  map_add' f g := by ext; simp
  map_smul' r f := by ext; simp [Algebra.smul_def]

private lemma evaluation_surjective (S : Finset (Fin 2 → k)) {n : ℕ} (hn : S.card ≤ n) :
    Function.Surjective (evaluate S n) := by
  classical
  /- A separate linear factor kills each of the other sample points. -/
  let axis (x y : S) := if x.val 0 = y.val 0 then (1 : Fin 2) else 0
  have axis_ne (x y : S) (h : x ≠ y) : x.val (axis x y) ≠ y.val (axis x y) := by
    dsimp [axis]
    split_ifs with h0
    · intro h1
      apply h
      apply Subtype.ext
      funext i
      fin_cases i <;> assumption
    · exact h0
  let lin (x y : S) : Poly k := X (axis x y) - C (y.val (axis x y))
  let delta (x : S) : Poly k := ∏ y ∈ univ.erase x, lin x y
  have deg (x : S) : (delta x).totalDegree ≤ n := by
    refine (totalDegree_finsetProd ..).trans ?_
    calc
      _ ≤ ∑ _y ∈ univ.erase x, 1 := sum_le_sum fun y _ => by
        dsimp [lin]
        apply (totalDegree_sub ..).trans
        simp
      _ ≤ n := by simp; omega
  have nonzero (x : S) : MvPolynomial.eval x.val (delta x) ≠ 0 := by
    simp only [delta,map_prod,lin,map_sub,eval_X,eval_C]
    exact prod_ne_zero_iff.mpr fun y hy => sub_ne_zero.mpr (axis_ne x y (mem_erase.mp hy).1.symm)
  have vanishes (x y : S) (hy : y ≠ x) : MvPolynomial.eval y.val (delta x) = 0 := by
    simp only [delta,map_prod,lin,map_sub,eval_X,eval_C]
    exact prod_eq_zero (mem_erase.mpr ⟨hy,mem_univ y⟩) (sub_self _)
  intro f
  let g (x : S) : Poly k := (f x / MvPolynomial.eval x.val (delta x)) • delta x
  refine ⟨⟨∑ x, g x,(mem_restrictTotalDegree _ _ _).mpr (totalDegree_finsetSum_le
    (fun x _ => (totalDegree_smul_le _ _).trans (deg x)))⟩, ?_⟩
  funext y
  change MvPolynomial.eval y.val (∑ x, g x) = f y
  rw [map_sum,sum_eq_single y]
  · simp [g,Algebra.smul_def,nonzero]
  · intro x _ hx
    simp [g,Algebra.smul_def,vanishes x y hx.symm]
  · simp

/-- Every finite set of common zeros of an irreducible plane polynomial F and a
polynomial G not divisible by F contains at most deg(F) deg(G) distinct points. -/
theorem common_zeros (F G : Poly k) (hF : Irreducible F) (hFG : ¬ F ∣ G)
    (S : Finset (Fin 2 → k)) (hf : ∀ x ∈ S, MvPolynomial.eval x F = 0)
    (hg : ∀ x ∈ S, MvPolynomial.eval x G = 0) :
    S.card ≤ F.totalDegree * G.totalDegree := by
  classical
  let n := S.card
  let d := F.totalDegree
  let e := G.totalDegree
  let m := n+d+e
  let A := times F (n+e) m (by dsimp [m,d]; omega)
  let B := times G (n+d) m (by dsimp [m,e]; omega)
  let L := A.coprod B
  let Y := evaluate S m
  let T := ((times (-G) n (n+e) (by simp [e]; omega))).prod
    (times F n (n+d) (by dsimp [d]; omega))
  have syz : LinearMap.ker L ≤ LinearMap.range T := by
    rintro ⟨a,b⟩ hab
    have eqn : F*a.val+G*b.val=0 := congrArg Subtype.val (LinearMap.mem_ker.mp hab)
    have div : F ∣ G*b.val := ⟨-a.val,by rw [mul_neg]; linear_combination eqn⟩
    obtain ⟨c,hc⟩ := ((hF.prime.dvd_mul.mp div).resolve_left hFG)
    have ha : a.val = (-G)*c := by
      apply mul_left_cancel₀ hF.ne_zero
      rw [hc] at eqn
      linear_combination eqn
    have cdeg : c.totalDegree ≤ n := by
      by_cases hz : c=0
      · simp [hz]
      · have hb := (mem_restrictTotalDegree _ _ _).mp b.prop
        rw [hc,totalDegree_mul_of_isDomain hF.ne_zero hz] at hb
        dsimp [d] at hb
        omega
    refine ⟨⟨c,(mem_restrictTotalDegree _ _ _).mpr cdeg⟩,?_⟩
    apply Prod.ext
    · exact Subtype.ext ha.symm
    · exact Subtype.ext hc.symm
  have inc : LinearMap.range L ≤ LinearMap.ker Y := by
    rintro _ ⟨⟨a,b⟩,rfl⟩
    apply LinearMap.mem_ker.mpr
    funext x
    change MvPolynomial.eval x.val (F*a.val+G*b.val) = 0
    simp [hf _ x.prop,hg _ x.prop]
  have surj : LinearMap.range Y = ⊤ := LinearMap.range_eq_top.mpr
    (evaluation_surjective S (by dsimp [m,n]; omega))
  have h₁ := L.finrank_range_add_finrank_ker
  have h₂ := Y.finrank_range_add_finrank_ker
  have h₃ := (Submodule.finrank_mono syz).trans (LinearMap.finrank_range_le T)
  have h₄ := Submodule.finrank_mono inc
  rw [surj,finrank_top,Module.finrank_pi, Fintype.card_coe] at h₂
  rw [Module.finrank_prod] at h₁
  have v₀ := degree_space_dimension k n
  have v₁ := degree_space_dimension k (n+e)
  have v₂ := degree_space_dimension k (n+d)
  have v₃ := degree_space_dimension k m
  dsimp only [m] at v₃
  change S.card ≤ d*e
  nlinarith only [h₁,h₂,h₃,h₄,v₀,v₁,v₂,v₃]

end
end PlanarUnitDistances.PlaneBezout
