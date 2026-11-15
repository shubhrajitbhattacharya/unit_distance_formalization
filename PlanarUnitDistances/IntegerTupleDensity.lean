import Mathlib.Order.Filter.Curry
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Basic

namespace PlanarUnitDistances.StationaryDeformation
open Filter MvPolynomial

/-- Integer choices are made successively. The exceptional set at each
step may depend on all preceding choices. -/
def integerTuples : (n : ℕ) → Filter (Fin n → ℕ)
  | 0 => pure Fin.elim0
  | n+1 => ((cofinite : Filter ℕ).curry (integerTuples n)).map
      (fun u : ℕ × (Fin n → ℕ) => Fin.cons u.1 u.2)

theorem eventually_cons {n : ℕ} {p : (Fin (n+1) → ℕ) → Prop} :
    (∀ᶠ x in integerTuples (n+1), p x) ↔
      ∀ᶠ a in cofinite, ∀ᶠ b in integerTuples n, p (Fin.cons a b) := Iff.rfl

instance neBot_integerTuples (n : ℕ) : (integerTuples n).NeBot := by
  induction n with
  | zero => dsimp [integerTuples]; infer_instance
  | succ n ih =>
    apply Filter.neBot_iff.mpr
    intro h
    have bad : ∀ᶠ _ in integerTuples (n+1), False := eventually_false_iff_eq_bot.mpr h
    obtain ⟨_, inner⟩ := (eventually_cons.mp bad).exists
    exact inner.exists.choose_spec

/-- Over a characteristic-zero domain, every nonzero polynomial survives
successive cofinite choices of ordinary nonnegative integers. -/
theorem eventually_integer_eval_ne_zero {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (n : ℕ) (F : MvPolynomial (Fin n) R) (nonzero : F ≠ 0) :
    ∀ᶠ t in integerTuples n, eval (fun i => (t i:R)) F ≠ 0 := by
  induction n with
  | zero =>
    obtain ⟨c,rfl⟩ := (isEmptyAlgEquiv R (Fin 0)).symm.surjective F
    simpa [integerTuples] using nonzero
  | succ n ih =>
    let f := finSuccEquiv R n F
    have nf : f ≠ 0 := (map_ne_zero_iff _ (finSuccEquiv R n).injective).mpr nonzero
    have good := (Nat.cast_injective (R := MvPolynomial (Fin n) R)).tendsto_cofinite.eventually
      (Polynomial.eventually_eval_ne_zero_cofinite nf)
    apply eventually_cons.mpr
    filter_upwards [good] with a ha
    filter_upwards [ih _ ha] with t ht
    have cons : (fun i : Fin (n+1) => ((Fin.cons (α := fun _ => ℕ) a t i : ℕ):R)) = Fin.cons (α := fun _ => R) (a:R) (fun i => (t i:R)) := by
      funext i
      exact Fin.cases (by simp) (fun j => by simp) i
    rw [cons, eval_eq_eval_mv_eval']
    have same := Polynomial.eval_map_apply (eval (fun i => (t i:R))) (p:=f) (a : MvPolynomial (Fin n) R)
    simpa [f] using fun h => ht (same.symm.trans (by simpa [f] using h))

end PlanarUnitDistances.StationaryDeformation
