import PlanarUnitDistances.AnchorEliminant
import PlanarUnitDistances.AnchorGenericPlane

namespace PlanarUnitDistances
open MvPolynomial Matrix AnchorFallback AnchorGenericPlane
open scoped Classical
noncomputable section
universe u

private theorem zero_aug_solution {L : Type*} [Field L] (x y b a r : Fin 4 → L)
    (h k A : L) (eqs : ∀ j,x j*h+y j*k-r j*A=b j-r j*a j) : (aug x y b a r).det=0 := by
  let w : Fin 4 → L := ![h,k,A,-1]
  apply det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors (v:=w) (i:=3)
  · funext j
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_four,aug,w]
    linear_combination eqs j
  · simp [w,mem_nonZeroDivisors_iff_ne_zero]

/-- The four-anchor lemma of the manuscript. One bivariate polynomial works
over all extension fields, including all singular specializations. -/
theorem four_anchor_curve {K : Type u} [Field K] [CharZero K] (I : K) (hI : I^2= -1)
    (r V : Fin 4 → Fin 2 → K) (a : Fin 4 → K) (hd : Function.Injective r) :
    ∃ F : MvPolynomial (Fin 2) K, F≠0 ∧ F.totalDegree ≤ 80 ∧
      ∀ (L : Type u) [Field L] (ι : K →+* L) (p H : Fin 2 → L) (A : L) (R : Fin 4 → L),
        (∀ j, let x := p 0-ι (r j 0)
              let y := p 1-ι (r j 1)
              let d := x^2+y^2
              R j^2=d*(d-4) ∧
                2*(x*(H 0-ι (V j 0))+y*(H 1-ι (V j 1)))=R j*(A-ι (a j))) →
        A ≠ ι (a 3) → MvPolynomial.eval₂ ι p F=0 := by
  let r₀ (j : Fin 4) := r j 0
  let r₁ (j : Fin 4) := r j 1
  let u (j : Fin 4) := V j 0
  let v (j : Fin 4) := V j 1
  let b := positionRhs r₀ r₁ u v
  let D (i : Fin 4) := radicand (r₀ i) (r₁ i)
  have inj : Function.Injective (fun j => (r₀ j,r₁ j)) := by
    intro i j hij
    apply hd
    funext k
    fin_cases k
    · exact congrArg Prod.fst hij
    · exact congrArg Prod.snd hij
  have degP (k : Fin 2) : (2*X k : Pol K).totalDegree ≤ 1 := by
    rw [show (2:Pol K)=C (2:K) from (map_ofNat C 2).symm]
    simpa using totalDegree_mul (C (2:K)) (X k)
  have posEq (i : Fin 2) (z : K) : (2*X i : Pol K)+C (-(2*z))=pos i z := by
    simp [pos,map_ofNat]; ring
  have degPos (i : Fin 2) (z : K) : (pos i z).totalDegree ≤ 1 := by
    rw [← posEq]
    exact (totalDegree_add _ _).trans (max_le (degP i) (by rw [totalDegree_C]; decide))
  have hb (j) : (b j).totalDegree ≤ 2 := by
    apply (totalDegree_add _ _).trans
    have h₀ := totalDegree_mul (pos 0 (r₀ j)) (C (u j))
    have h₁ := totalDegree_mul (pos 1 (r₁ j)) (C (v j))
    simp only [totalDegree_C,add_zero] at h₀ h₁
    exact max_le ((h₀.trans (degPos ..)).trans (by decide)) ((h₁.trans (degPos ..)).trans (by decide))
  obtain ⟨F,dF,forward,back⟩ := RadicalNorm.four_root_eliminant
    (2*X 0) (2*X 1) (fun j => -(2*r₀ j)) (fun j => -(2*r₁ j))
    b (fun j => C (a j)) D (degP _) (degP _) hb (fun _ => by simp) (fun _ => radicand_degree _ _)
  simp only [posEq] at forward back
  by_cases hz : F=0
  · let K' := Frac2 K
    let φ := algebraMap K' (AlgebraicClosure K')
    obtain ⟨t,st,det⟩ := back (φ.comp (Dx I)) (by rw [hz,map_zero])
    obtain ⟨m⟩ := exists_generic_roots hI r₀ r₁ inj
    have z := genericAug_zero_from_chosen_roots r₀ r₁ u v a m φ t st det
    obtain ⟨Q,hQ,dQ,van⟩ := cartesian_fallback hI r₀ r₁ u v a inj m z
    refine ⟨Q,hQ,dQ.trans (by decide),?_⟩
    intro L _ ι p H A R he ne
    have peq : ![p 0,p 1]=p := by funext i; fin_cases i <;> rfl
    have hv := van L ι (p 0) (p 1) (H 0) (H 1) A R (fun j => (he j).1) (fun j => (he j).2) ne
    rwa [peq] at hv
  · refine ⟨F,hz,dF,?_⟩
    intro L _ ι p H A R he _
    apply forward (eval₂Hom ι p) R
    · intro j; simpa [D,radicand,distanceSq,r₀,r₁] using (he j).1
    · apply zero_aug_solution _ _ _ _ _ (H 0) (H 1) A
      intro j
      simp [pos,b,positionRhs,r₀,r₁,u,v]
      linear_combination (he j).2

end
end PlanarUnitDistances
