import Mathlib.Analysis.Complex.Polynomial.Basic
import PlanarUnitDistances.PositionSystem
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.BigOperators.Associated

namespace PlanarUnitDistances.Competition.GenericCurvePoint
open MvPolynomial Finset
noncomputable section

def abscissas (f : Poly₂) : Set ℂ :=
  {a | ∃ x : Fin 2 → ℂ, eval x f=0 ∧ x 0=a}

/-- An irreducible plane curve with two distinct abscissas has infinitely
many. This uses Mathlib's Nullstellensatz for the principal prime ideal. -/
theorem infinite_abscissas {f : Poly₂} (irr : Irreducible f)
    (nonconstant : ∃ p r : Fin 2 → ℂ,eval p f=0 ∧ eval r f=0 ∧ p 0≠r 0) :
    (abscissas f).Infinite := by
  classical
  intro finite
  let T := finite.toFinset
  let J := Ideal.span ({f}:Set Poly₂)
  let _ : J.IsPrime := (Ideal.span_singleton_prime irr.ne_zero).mpr irr.prime
  let P : Poly₂ := ∏ a∈T,(X 0-C a)
  have vanish : P∈vanishingIdeal ℂ (zeroLocus ℂ J) := by
    intro x hx
    have hf := hx f (Ideal.subset_span (Set.mem_singleton _))
    have ha : x 0∈T := finite.mem_toFinset.mpr ⟨x,hf,rfl⟩
    change eval x P=0
    simp only [P,map_prod,map_sub,eval_X,eval_C]
    exact Finset.prod_eq_zero ha (sub_self _)
  have div : f∣P := by
    apply Ideal.mem_span_singleton.mp
    change P∈J
    rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) J] at vanish
    exact vanish
  obtain ⟨a,_,q,hq⟩ := (irr.prime.dvd_finsetProd_iff (fun a : ℂ => X 0-C a)).mp div
  have c (x : Fin 2 → ℂ) (h : eval x f=0) : x 0=a := by
    have z := congrArg (eval x) hq
    have v : x 0-a=0 := by simpa [h] using z
    exact sub_eq_zero.mp v
  obtain ⟨p,r,hp,hr,ne⟩ := nonconstant
  exact ne ((c p hp).trans (c r hr).symm)

/-- No nonzero polynomial in the twelve abscissas vanishes on the whole
product. The finite-dimensional product only needs infinite coordinate
images. -/
theorem product_abscissas {f g : Poly₂} (pair : CurvePair f g)
    (p : MvPolynomial Slot ℂ) (hne : p≠0) :
    ∃ x ∈ curveProduct f g, eval (fun s => x (s,0)) p≠0 := by
  classical
  let h (s : Slot) := s.elim (fun _ => f) (fun _ => g)
  have inf (s : Slot) : (abscissas (h s)).Infinite := by
    have H := pair.1 (h s) (by cases s <;> simp [h])
    exact infinite_abscissas H.1 (H.2.2 0)
  have exists_z : ∃ z ∈ Set.pi Set.univ (fun s => abscissas (h s)), eval z p≠0 := by
    by_contra! fail
    apply hne
    exact MvPolynomial.funext_set (fun s => abscissas (h s)) inf
      (fun z hz => (fail z hz).trans (map_zero _).symm)
  obtain ⟨z,hz,hval⟩ := exists_z
  choose row on ab using fun s => hz s (Set.mem_univ s)
  refine ⟨fun (i : Coord) => row i.1 i.2,⟨fun i => on (.inl i),fun j => on (.inr j)⟩,?_⟩
  simpa only [ab] using hval

end
end PlanarUnitDistances.Competition.GenericCurvePoint
