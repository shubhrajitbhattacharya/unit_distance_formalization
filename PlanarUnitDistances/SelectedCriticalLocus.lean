import PlanarUnitDistances.CriticalLocus

namespace PlanarUnitDistances.CriticalLocus
open MvPolynomial
noncomputable section

variable {k X E R : Type*} [Field k] [Fintype R]


/-- Keep the chosen primal equations, their multiplier equations, and the output equation. -/
def selectedIdeal (f : MvPolynomial X k) (g : E → MvPolynomial X k) (pick : R → E) :
    Ideal (MvPolynomial (Variables X R) k) :=
  incidenceIdeal f (g ∘ pick) id


theorem selectedIdeal_le (f : MvPolynomial X k) (g : E → MvPolynomial X k) (pick : R → E) :
    selectedIdeal f g pick ≤ incidenceIdeal f g pick := by
  apply Ideal.span_le.mpr
  rintro _ ⟨e | h, rfl⟩
  · exact Ideal.subset_span ⟨.inl (pick e), rfl⟩
  · cases h with
    | inl x => exact Ideal.subset_span ⟨.inr (.inl x), rfl⟩
    | inr u => exact Ideal.subset_span ⟨.inr (.inr u), rfl⟩

/-- Each component of the full multiplier system lies on a component of the
selected system with the same constant output. This uses constancy on the
larger component, including when the full component has smaller dimension. -/
theorem constant_on_selected_component [Fintype X] [CharZero k] [IsAlgClosed k]
    (f : MvPolynomial X k) (g : E → MvPolynomial X k) (pick : R → E)
    (P : Ideal (MvPolynomial (Variables X R) k)) [P.IsPrime]
    (hP : incidenceIdeal f g pick ≤ P) (c : k) (hc : outputVariable - C c ∈ P) :
    ∃ Q ∈ (selectedIdeal f g pick).minimalPrimes,
      Q ≤ P ∧ outputVariable - C c ∈ Q := by
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le ((selectedIdeal_le f g pick).trans hP)
  have := hQ.isPrime
  obtain ⟨d, hd⟩ := output_constant_mod_prime f (g ∘ pick) id Q hQ.le
  let q := Ideal.Quotient.mkₐ k P
  have coordinate (b : k) (hb : outputVariable - C b ∈ P) :
      q outputVariable = algebraMap k _ b := by
    have hz : q (outputVariable - C b) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
    rw [map_sub, sub_eq_zero] at hz
    exact hz.trans (q.commutes b)
  have hcd : c = d := (algebraMap k _).injective
    ((coordinate c hc).symm.trans (coordinate d (hQP hd)))
  exact ⟨Q, hQ, hQP, hcd ▸ hd⟩

end
end PlanarUnitDistances.CriticalLocus
