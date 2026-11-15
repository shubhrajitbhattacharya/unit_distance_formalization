import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! A witness-slicing proof of the zero count on a product of curves. Different coordinates may have different
ambient types. The input from plane geometry is the one-variable bound for
a non-identically-zero restriction (Bézout in the application). -/

namespace PlanarUnitDistances.ProductZeros

open Finset Fintype

/-- Count zero tuples in an arbitrary finite box. The predicate and the
nonzero witness live on the entire ambient product. The witness need not
belong to the sampled box. -/
theorem card_zeros_le {s : ℕ} (C : Fin s → Type*) (S : ∀ i, Finset (C i))
    (Z : (∀ i, C i) → Prop) [DecidablePred Z] (m n : ℕ)
    (size : ∀ i, (S i).card ≤ n)
    (slice : ∀ (x : ∀ i, C i) (i : Fin s), ¬ Z x →
      ((S i).filter fun t => Z (Function.update x i t)).card ≤ m)
    (w : ∀ i, C i) (hw : ¬ Z w) :
    ((piFinset S).filter Z).card ≤ s * m * n ^ (s - 1) := by
  classical
  induction s with
  | zero =>
    have h : (piFinset S).filter Z = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro x _ hx
      exact hw (Subsingleton.elim x w ▸ hx)
    rw [h, Finset.card_empty]
    exact Nat.zero_le _
  | succ s ih =>
    let T := piFinset (Fin.tail S)
    let Z' (t : ∀ j : Fin s, C j.succ) := Z (Fin.cons (w 0) t)
    have htail : (T.filter Z').card ≤ s * m * n ^ (s - 1) := by
      refine ih _ (Fin.tail S) Z' (fun j => size j.succ) ?_ (Fin.tail w) ?_
      · intro x i hx
        simpa only [Z', Fin.cons_update, Fin.tail] using slice (Fin.cons (w 0) x) i.succ hx
      · simpa [Z'] using hw
    let roots := (piFinset S).filter Z
    have intoT : (roots : Set (∀ i, C i)).MapsTo Fin.tail T := by
      intro x hx
      exact (Fin.mem_piFinset_iff_zero_tail.mp (mem_filter.mp hx).1).2
    have bound (t : ∀ j : Fin s, C j.succ) :
        (roots.filter fun x => Fin.tail x = t).card ≤ m + (if Z' t then n else 0) := by
      have hcard : (roots.filter fun x => Fin.tail x = t).card ≤
          ((S 0).filter fun a => Z (Fin.cons a t)).card := by
        apply card_le_card_of_injOn (fun x => x 0)
        · intro x hx
          obtain ⟨hx₁, ht⟩ := mem_filter.mp hx
          obtain ⟨hx₂, hxZ⟩ := mem_filter.mp hx₁
          exact mem_filter.mpr ⟨(mem_piFinset.mp hx₂) 0, by simpa [← ht] using hxZ⟩
        · intro x hx y hy hxy
          change x 0 = y 0 at hxy
          have ht : Fin.tail x = Fin.tail y := (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm
          calc
            x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
            _ = Fin.cons (y 0) (Fin.tail y) := by rw [hxy, ht]
            _ = y := Fin.cons_self_tail y
      by_cases hz : Z' t
      · exact hcard.trans ((card_filter_le _ _).trans ((size 0).trans (by simp [hz])))
      · have h := slice (Fin.cons (w 0) t) 0 hz
        simpa only [Fin.update_cons_zero, if_neg hz, add_zero] using hcard.trans
          (by simpa only [Fin.update_cons_zero] using h)
    have cardT : T.card ≤ n ^ s := by
      calc
        T.card = ∏ i : Fin s, (S i.succ).card := Fintype.card_piFinset _
        _ ≤ ∏ _ : Fin s, n := Finset.prod_le_prod' (fun i _ => size i.succ)
        _ = n ^ s := by simp
    change roots.card ≤ _
    calc
      roots.card = ∑ t ∈ T, (roots.filter fun x => Fin.tail x = t).card :=
        card_eq_sum_card_fiberwise intoT
      _ ≤ ∑ t ∈ T, (m + if Z' t then n else 0) := sum_le_sum fun t _ => bound t
      _ = T.card * m + (T.filter Z').card * n := by
        rw [sum_add_distrib, ← sum_filter Z' (fun _ => n)]
        simp
      _ ≤ n ^ s * m + (s * m * n ^ (s - 1)) * n := by gcongr
      _ = (s + 1) * m * n ^ (s + 1 - 1) := by
        cases s with
        | zero => simp
        | succ s => simp only [Nat.add_sub_cancel, pow_succ]; ring

/-- Substituting the one-curve Bézout bound gives the precise degree factor
of the manuscript. Only the one-curve intersection assertion is assumed. -/
theorem curve_product_bound {s : ℕ} (C : Fin s → Type*) (S : ∀ i, Finset (C i))
    {K : Type*} [Zero K] (F : (∀ i, C i) → K) [DecidableEq K] (D E n : ℕ)
    (size : ∀ i, (S i).card ≤ n)
    (bezout : ∀ (x : ∀ i, C i) (i : Fin s), F x ≠ 0 →
      ((S i).filter fun t => F (Function.update x i t) = 0).card ≤ D * E)
    (w : ∀ i, C i) (hw : F w ≠ 0) :
    ((piFinset S).filter fun x => F x = 0).card ≤ s * D * E * n ^ (s - 1) := by
  simpa only [Nat.mul_assoc] using
    card_zeros_le C S (fun x => F x = 0) (D * E) n size bezout w hw

end PlanarUnitDistances.ProductZeros
