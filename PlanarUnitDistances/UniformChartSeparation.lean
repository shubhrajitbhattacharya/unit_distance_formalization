import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

namespace PlanarUnitDistances.UniformSeparation
open MvPolynomial Finset
open scoped Classical
noncomputable section
variable {k σ : Type*} [Field k]

abbrev Chart (σ k : Type*) [Field k] := Finset (MvPolynomial σ k) × MvPolynomial σ k

def Holds (a : Chart σ k) (x : σ → k) : Prop :=
  (∀ f ∈ a.1, eval x f=0) ∧ eval x a.2 ≠ 0

def NonzeroOn (W : Set (σ → k)) (f : MvPolynomial σ k) : Prop :=
  ∃ x ∈ W, eval x f ≠ 0

private theorem separate_one (W : Set (σ → k)) (a : Chart σ k) (g : MvPolynomial σ k)
    (hg : NonzeroOn W g) (vanish : ∀ x ∈ W, Holds a x → eval x g=0)
    (product : ∀ p q, NonzeroOn W p → NonzeroOn W q → NonzeroOn W (p*q)) :
    ∃ f : MvPolynomial σ k, f.totalDegree ≤ ∑h∈a.1,h.totalDegree ∧
      (∀ x ∈ W, Holds a x → eval x f=0) ∧ NonzeroOn W f := by
  classical
  by_cases existsEq : ∃ f ∈ a.1, NonzeroOn W f
  · obtain ⟨f,hf,pos⟩ := existsEq
    exact ⟨f,single_le_sum (fun _ _ => Nat.zero_le _) hf,fun _ _ hx => hx.1 f hf,pos⟩
  · have closed (x : σ→k) (hx : x∈W) (f) (hf : f∈a.1) : eval x f=0 := by
      by_contra h
      exact existsEq ⟨f,hf,x,hx,h⟩
    have empty (x : σ→k) (hx : x∈W) (ha : Holds a x) : False := by
      obtain ⟨y,hy,hprod⟩ := product a.2 g ⟨x,hx,ha.2⟩ hg
      rw [map_mul] at hprod
      have guard : eval y a.2 ≠ 0 := left_ne_zero_of_mul hprod
      exact (right_ne_zero_of_mul hprod) (vanish y hy ⟨closed y hy,guard⟩)
    obtain ⟨y,hy,_⟩ := hg
    refine ⟨1,by simp,fun x hx ha => (empty x hx ha).elim,y,hy,by simp⟩

/-- A fixed constructible description gives a single degree bound for all
irreducible test sets. The degree of a supplied separator can vary arbitrarily
with the test set. Only its nonvanishing and vanishing properties enter. -/
theorem uniform_separator {S : Set (σ → k)} (T : Finset (Chart σ k))
    (charts : ∀x,x∈S ↔ ∃ a ∈ T,Holds a x) :
    ∃ E : ℕ, ∀ W : Set (σ → k),
      (∀ p q, NonzeroOn W p → NonzeroOn W q → NonzeroOn W (p*q)) →
      (∃ g : MvPolynomial σ k, NonzeroOn W g ∧ ∀ x ∈ W, x∈S → eval x g=0) →
      ∃ f : MvPolynomial σ k, f.totalDegree ≤ E ∧
        (∀ x ∈ W, x∈S → eval x f=0) ∧ NonzeroOn W f := by
  classical
  let cost (a : Chart σ k) := ∑h∈a.1,h.totalDegree
  refine ⟨∑a∈T,cost a,?_⟩
  rintro W product ⟨g,hg,zero⟩
  have each (a) (ha : a∈T) := separate_one W a g hg
    (fun x hx h => zero x hx ((charts x).mpr ⟨a,ha,h⟩)) product
  choose f degree vanishes nonzero using each
  let F (a : Chart σ k) := if h : a∈T then f a h else 1
  have pos (J : Finset (Chart σ k)) (sub : J ⊆ T) : NonzeroOn W (∏a∈J,F a) := by
    induction J using Finset.induction_on with
    | empty =>
      obtain ⟨x,hx,_⟩ := hg
      exact ⟨x,hx,by simp⟩
    | @insert a J ha ih =>
      rw [prod_insert ha]
      have mem := sub (mem_insert_self a J)
      exact product _ _ (by simpa only [F,dif_pos mem] using nonzero a mem)
        (ih (fun _ h => sub (mem_insert_of_mem h)))
  refine ⟨∏a∈T,F a,(totalDegree_finsetProd T F).trans ?_,?_,pos T (Subset.rfl)⟩
  · apply sum_le_sum; intro a ha
    simpa only [F,dif_pos ha] using degree a ha
  · intro x hx hs
    obtain ⟨a,ha,h⟩ := (charts x).mp hs
    rw [map_prod]
    apply prod_eq_zero ha
    simpa only [F,dif_pos ha] using vanishes a ha x hx h

end
end PlanarUnitDistances.UniformSeparation
