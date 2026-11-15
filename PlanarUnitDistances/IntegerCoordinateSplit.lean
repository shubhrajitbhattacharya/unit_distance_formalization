import PlanarUnitDistances.IntegralSubstitutionSize

namespace PlanarUnitDistances.IntegralCoordinateSplit
open MvPolynomial EliminantHeight Finsupp Finset
noncomputable section


theorem split_sum_coeff {R α β : Type*} [CommSemiring R]
    (p : MvPolynomial (α ⊕ β) R) (a : α →₀ ℕ) (b : β →₀ ℕ) :
    (((sumAlgEquiv R α β p).coeff a).coeff b) =
      p.coeff (sumFinsuppAddEquivProdFinsupp.symm (a,b)) := by
  change (AddMonoidAlgebra.domCongr R R sumFinsuppAddEquivProdFinsupp p).coeff (a,b) = _
  exact AddMonoidAlgebra.coeff_domCongr ..


theorem sum_coeff_bound {α β : Type*} (p : MvPolynomial (α ⊕ β) ℤ) (a : α →₀ ℕ) :
    coefficientSum ((sumAlgEquiv ℤ α β p).coeff a) ≤ coefficientSum p := by
  classical
  let T := ((sumAlgEquiv ℤ α β p).coeff a).support
  let join (b : β →₀ ℕ) : (α ⊕ β) →₀ ℕ := sumFinsuppAddEquivProdFinsupp.symm (a,b)
  have inj : Function.Injective join := fun _ _ h => congrArg Prod.snd (sumFinsuppAddEquivProdFinsupp.symm.injective h)
  have sub : T.image join ⊆ p.support := by
    intro u hu
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hu
    exact MvPolynomial.mem_support_iff.mpr (by
      simpa only [join, ←split_sum_coeff] using MvPolynomial.mem_support_iff.mp hb)
  have h := sum_le_sum_of_subset_of_nonneg (f:=fun d => (p.coeff d).natAbs) sub (by intros; omega)
  rw [sum_image (fun _ _ _ _ e => inj e)] at h
  simpa only [coefficientSum, split_sum_coeff, T, join] using h


theorem sum_coeff_degree {R α β : Type*} [CommSemiring R] [Fintype α] [Fintype β]
    (p : MvPolynomial (α ⊕ β) R) (a : α →₀ ℕ) :
    ((sumAlgEquiv R α β p).coeff a).totalDegree ≤ p.totalDegree := by
  classical
  apply Finset.sup_le
  intro b hb
  let d : (α ⊕ β) →₀ ℕ := sumFinsuppAddEquivProdFinsupp.symm (a,b)
  have mem : d ∈ p.support := MvPolynomial.mem_support_iff.mpr
    (by simpa only [d, ← split_sum_coeff] using MvPolynomial.mem_support_iff.mp hb)
  apply le_trans _ (le_totalDegree mem)
  change b.degree ≤ d.degree
  rw [degree_eq_sum, degree_eq_sum, Fintype.sum_sum_type]
  have h (i : β) : d (.inr i) = b i := rfl
  simp only [h]
  omega


end
end PlanarUnitDistances.IntegralCoordinateSplit
