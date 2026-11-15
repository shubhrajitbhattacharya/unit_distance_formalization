import PlanarUnitDistances.IntegralSliceAvoidance
import PlanarUnitDistances.IntegerTupleDensity
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

namespace PlanarUnitDistances.StationaryDeformation
open Filter
noncomputable section
variable {R k : Type*} [CommRing R] [IsNoetherianRing R] [Field k] [CharZero k] [Algebra k R]
variable {w : ℕ}

def combination (g : Fin w → R) (a : ℕ) : R := ∑ i : Fin w, (a:R)^(i:ℕ)*g i

omit [IsNoetherianRing R] in
theorem combination_mem (g : Fin w → R) (a : ℕ) :
    combination g a ∈ Ideal.span (Set.range g) :=
  Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,rfl⟩)

include k in
/-- After j cuts, all minimal components strictly below the prescribed prime
have height at least j. Almost every next integer combination increases this
lower bound, because it misses all those components at once. -/
theorem generic_cut_step (g : Fin w → R) (P J : Ideal R)
    (minimal : P ∈ (Ideal.span (Set.range g)).minimalPrimes) (j : ℕ)
    (lower : ∀ Q ∈ J.minimalPrimes, Q < P → (j : ℕ∞) ≤ Q.height) :
    ∀ᶠ a : ℕ in cofinite, ∀ Q' ∈ (J ⊔ Ideal.span {combination g a}).minimalPrimes,
      Q' < P → ((j+1:ℕ):ℕ∞) ≤ Q'.height := by
  classical
  let primes := J.finite_minimalPrimes_of_isNoetherianRing.toFinset.filter (· < P)
  have mem (Q : Ideal R) : Q ∈ primes ↔ Q ∈ J.minimalPrimes ∧ Q < P := by simp [primes]
  have good := cofinite_prime_avoidance (k:=k) g primes
    (fun Q h => ((mem Q).mp h).1.isPrime) (fun Q h => by
      obtain ⟨hq,strict⟩ := (mem Q).mp h
      by_contra! all
      have contain : Ideal.span (Set.range g) ≤ Q := Ideal.span_le.mpr (by
        rintro x ⟨i,rfl⟩
        exact all i)
      exact strict.not_ge (minimal.2 ⟨hq.isPrime,contain⟩ strict.le))
  filter_upwards [good] with a ha Q' newQ ltP
  let := newQ.isPrime
  obtain ⟨Q, hQ, below⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans newQ.le : J ≤ Q')
  let := hQ.isPrime
  have hQP := lt_of_le_of_lt below ltP
  have avoided := ha Q ((mem Q).mpr ⟨hQ,hQP⟩)
  have cutMem : combination g a ∈ Q' :=
    (le_sup_right.trans newQ.le : Ideal.span {combination g a} ≤ Q')
      (Ideal.subset_span (Set.mem_singleton _))
  have strict : Q < Q' := lt_of_le_of_ne below (fun e => avoided (e ▸ cutMem))
  exact_mod_cast (add_le_add (lower Q hQ hQP) (le_refl (1 : ℕ∞))).trans
    (Ideal.height_add_one_le_of_lt_of_isPrime strict)

def cuts (g : Fin w → R) : (n : ℕ) → (Fin n → ℕ) → Ideal R → Ideal R
  | 0, _, J => J
  | n+1, a, J => cuts g n (Fin.tail a) (J ⊔ Ideal.span {combination g (a 0)})

omit [IsNoetherianRing R] in
theorem cuts_eq (g : Fin w → R) (n : ℕ) (a : Fin n → ℕ) (J : Ideal R) :
    cuts g n a J = J ⊔ Ideal.span (Set.range (fun i => combination g (a i))) := by
  induction n generalizing J with
  | zero => simp [cuts]
  | succ n ih =>
    have range_eq : Set.range (fun i => combination g (a i)) =
        {combination g (a 0)} ∪ Set.range (fun i => combination g (Fin.tail a i)) := by
      ext x
      constructor
      · rintro ⟨i,rfl⟩
        exact Fin.cases (Or.inl rfl) (fun j => Or.inr ⟨j,rfl⟩) i
      · rintro (h | ⟨i,rfl⟩)
        · exact ⟨0, h.symm⟩
        · exact ⟨_,rfl⟩
    rw [cuts,ih,range_eq,Ideal.span_union,sup_assoc]

include k in
theorem generic_cuts_bound (g : Fin w → R) (P : Ideal R)
    (hP : P ∈ (Ideal.span (Set.range g)).minimalPrimes) (n j : ℕ) (J : Ideal R)
    (lower : ∀ Q ∈ J.minimalPrimes, Q < P → (j : ℕ∞) ≤ Q.height) :
    ∀ᶠ a in integerTuples n, ∀ Q ∈ (cuts g n a J).minimalPrimes, Q < P → ((j+n:ℕ):ℕ∞) ≤ Q.height := by
  induction n generalizing j J with
  | zero => simpa [cuts,integerTuples] using lower
  | succ n ih =>
    apply eventually_cons.mpr
    filter_upwards [generic_cut_step (k:=k) g P J hP j lower] with a ha
    have inner := ih (j+1) (J ⊔ Ideal.span {combination g a}) ha
    simpa [cuts, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using inner

include k in
/-- As many combinations as the height of P isolate P locally. The nested
cofinite quantifiers allow extraction of polynomial coefficients in the mixing
parameters after the geometric argument. -/
theorem generic_square_selection (g : Fin w → R) (P : Ideal R)
    (hP : P ∈ (Ideal.span (Set.range g)).minimalPrimes) (n : ℕ) (height : P.height=n) :
    ∀ᶠ a in integerTuples n, P ∈ (Ideal.span (Set.range (fun i => combination g (a i)))).minimalPrimes := by
  classical
  let := hP.isPrime
  filter_upwards [generic_cuts_bound (k:=k) g P hP n 0 ⊥ (by simp)] with a ha
  let J := Ideal.span (Set.range (fun i => combination g (a i)))
  have subset : J ≤ P := Ideal.span_le.mpr (by rintro x ⟨i,rfl⟩; exact hP.le (combination_mem g _))
  obtain ⟨Q,hQ,le⟩ := Ideal.exists_minimalPrimes_le subset
  suffices Q = P by simpa [this] using hQ
  by_contra ne
  have strict := lt_of_le_of_ne le ne
  let := hQ.isPrime
  have jm : Q ∈ (cuts g n a ⊥).minimalPrimes := by simpa [cuts_eq,J] using hQ
  have bound : (n:ℕ∞) ≤ Q.height := by simpa using ha Q jm strict
  have step := (add_le_add bound (le_refl (1:ℕ∞))).trans (Ideal.height_add_one_le_of_lt_of_isPrime strict)
  rw [height] at step
  exact (by exact_mod_cast Nat.not_succ_le_self n : ¬ (n:ℕ∞)+1≤n) step

end
end PlanarUnitDistances.StationaryDeformation
