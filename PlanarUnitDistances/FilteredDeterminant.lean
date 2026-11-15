import PlanarUnitDistances.QuadraticFiltration
import PlanarUnitDistances.AnchorFallback
namespace PlanarUnitDistances.RadicalNorm
open MvPolynomial Matrix Finset
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R]
private theorem det_row_differences (M : Matrix (Fin 4) (Fin 4) R) :
    Matrix.det (fun i j => if i=0 then M i j else M i j-M 0 j) = M.det := by
  let A := M.updateRow 1 (M 1 + (-1 : R) • M 0)
  let B := A.updateRow 2 (A 2 + (-1 : R) • A 0)
  let C' := B.updateRow 3 (B 3 + (-1 : R) • B 0)
  have eqC : (fun i j => if i=0 then M i j else M i j-M 0 j) = C' := by
    ext i j
    fin_cases i <;> simp [A,B,C',updateRow,Function.update,sub_eq_add_neg]
  rw [eqC]
  exact (det_updateRow_add_smul_self B (by decide : (3:Fin 4)≠0) _).trans
    ((det_updateRow_add_smul_self A (by decide : (2:Fin 4)≠0) _).trans
    (det_updateRow_add_smul_self M (by decide : (1:Fin 4)≠0) _))


private theorem sumFits {I : Type*} (b : Bounds R) (s : Finset I) (v : I → R) (n : ℤ)
    (h : ∀ i ∈ s, b.fits n (v i)) : b.fits n (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using b.zero n
  | insert i s hi ih =>
    rw [sum_insert hi]
    exact b.add (h i (mem_insert_self ..)) (ih (fun j hj => h j (mem_insert_of_mem hj)))

private theorem prodFits {I : Type*} (b : Bounds R) (s : Finset I) (v : I → R) (n : I → ℤ)
    (h : ∀ i ∈ s, b.fits (n i) (v i)) : b.fits (∑ i ∈ s,n i) (∏ i ∈ s,v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using b.one
  | insert i s hi ih =>
    rw [sum_insert hi,prod_insert hi]
    exact b.mul (h i (mem_insert_self ..)) (ih (fun j hj => h j (mem_insert_of_mem hj)))

private theorem detFits (b : Bounds R) (M : Matrix (Fin 4) (Fin 4) R)
    (v : Fin 4 → Fin 4 → ℤ) (hv : ∀ i j, b.fits (v i j) (M i j))
    (h : ∀ s : Equiv.Perm (Fin 4), ∑ j, v (s j) j ≤ 5) : b.fits 5 M.det := by
  rw [Matrix.det_apply]
  apply sumFits
  intro s _
  have hp := b.mono (h s) (prodFits b univ (fun j => M (s j) j) (fun j => v (s j) j) (fun j _ => hv _ _))
  simp only [Units.smul_def]
  rcases Int.isUnit_eq_one_or (Equiv.Perm.sign s).isUnit with hs | hs
  · simpa [hs] using hp
  · simpa [hs] using b.neg hp

/-- Weighted degree five for the actual augmented determinant inside the
iterated square-root algebra. The two affine columns have a common leading term. -/
theorem augmentedFits (b : Bounds R) (M : Matrix (Fin 4) (Fin 4) R)
    (p q : R) (a c : Fin 4 → R) (hp : b.fits 1 p) (hq : b.fits 1 q)
    (ha : ∀ i, b.fits 0 (a i)) (hc : ∀ i, b.fits 0 (c i))
    (h0 : ∀ i, M i 0=p+a i) (h1 : ∀ i, M i 1=q+c i)
    (h2 : ∀ i, b.fits 2 (M i 2)) (h3 : ∀ i, b.fits 2 (M i 3)) : b.fits 5 M.det := by
  let D : Matrix (Fin 4) (Fin 4) R := fun i j => if i=0 then M i j else M i j-M 0 j
  let w (i : Fin 4) : Fin 4 → ℤ := ![if i=0 then 1 else 0,if i=0 then 1 else 0,2,2]
  have left (i j : Fin 4) (u : R) (v : Fin 4 → R) (H : ∀ k, M k j=u+v k)
      (hu : b.fits 1 u) (hv : ∀ l, b.fits 0 (v l)) :
      b.fits (if i=0 then 1 else 0) (D i j) := by
    by_cases hi : i=0
    · simp only [D,hi,if_true,H]
      exact b.add hu (b.mono (by decide : (0:ℤ)≤1) (hv _))
    · simp only [D,if_neg hi,H]
      rw [add_sub_add_left_eq_sub,sub_eq_add_neg]
      exact b.add (hv _) (b.neg (hv _))
  have right (i j : Fin 4) (h : ∀ l, b.fits 2 (M l j)) : b.fits 2 (D i j) := by
    by_cases hi : i=0
    · simpa [D,hi] using h 0
    · simpa [D,hi,sub_eq_add_neg] using b.add (h i) (b.neg (h 0))
  rw [← det_row_differences M]
  apply detFits b D w
  · intro i j
    fin_cases j
    · exact left i 0 p a h0 hp ha
    · exact left i 1 q c h1 hq hc
    · exact right i 2 h2
    · exact right i 3 h3
  · intro s
    have ne := s.injective.ne (by decide : (0:Fin 4)≠1)
    simp [w,Fin.sum_univ_four]
    split_ifs <;> omega

end
end PlanarUnitDistances.RadicalNorm
