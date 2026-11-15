import PlanarUnitDistances.FormalRoots
import PlanarUnitDistances.FilteredDeterminant

namespace PlanarUnitDistances.RadicalNorm
open MvPolynomial Matrix AnchorFallback
open scoped Classical
noncomputable section
universe u
variable {k : Type u} [Field k]
abbrev PP (k : Type u) [Field k] := MvPolynomial (Fin 2) k

private theorem polyFits {p : PP k} {n : ℕ} (h : p.totalDegree ≤ n) :
    (polynomialBounds (Fin 2) k).fits n p := Or.inr (by exact_mod_cast h)

private theorem map_aug_det {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (x y b a r : Fin 4 → R) :
    g (aug x y b a r).det = (aug (g ∘ x) (g ∘ y) (g ∘ b) (g ∘ a) (g ∘ r)).det := by
  rw [g.map_det]
  congr 1
  ext i j
  fin_cases j <;> simp [aug]

/-- The eliminant of the four-row equations. It has degree at most 80,
vanishes for every actual solution, and any zero lifts to a determinant zero
over an algebraically closed field. No generic-rank condition is imposed. -/
private theorem eliminant_of_model (p q : PP k) (u v : Fin 4 → k)
    (b a D : Fin 4 → PP k) (hp : p.totalDegree ≤ 1) (hq : q.totalDegree ≤ 1)
    (hb : ∀ j, (b j).totalDegree ≤ 2) (ha : ∀ j, (a j).totalDegree ≤ 0)
    (t : RootModel (polynomialBounds (Fin 2) k) D) :
    let x := fun i => p+C (u i)
    let y := fun i => q+C (v i)
    ∃ Q : PP k, Q.totalDegree ≤ 80 ∧
      (∀ {L : Type u} [Field L] (f : PP k →+* L) (r : Fin 4 → L),
        (∀ j, (r j)^2=f (D j)) →
        (aug (f ∘ x) (f ∘ y) (f ∘ b) (f ∘ a) r).det=0 → f Q=0) ∧
      (∀ {L : Type u} [Field L] [IsAlgClosed L] (f : PP k →+* L), f Q=0 →
        ∃ r : Fin 4 → L, (∀ j, (r j)^2=f (D j)) ∧
          (aug (f ∘ x) (f ∘ y) (f ∘ b) (f ∘ a) r).det=0) := by
  let x := fun i => p+C (u i)
  let y := fun i => q+C (v i)
  let e := t.tower.incl
  let M := aug (e ∘ x) (e ∘ y) (e ∘ b) (e ∘ a) t.root
  have con (z : k) : t.c.fits 0 (e (C z)) := t.baseSmall (Or.inr (by simp))
  have deg : t.c.fits 5 M.det := by
    apply augmentedFits t.c M (e p) (e q) (fun i => e (C (u i))) (fun i => e (C (v i)))
      (t.baseSmall (polyFits hp)) (t.baseSmall (polyFits hq)) (fun _ => con _) (fun _ => con _)
    · intro i; exact map_add e _ _
    · intro i; exact map_add e _ _
    · intro i; exact t.c.neg (t.small i)
    · intro i
      change t.c.fits 2 (e (b i)-t.root i*e (a i))
      rw [sub_eq_add_neg]
      exact t.c.add (t.baseSmall (polyFits (hb i)))
        (t.c.neg (t.c.mul (t.small i) (t.baseSmall (polyFits (ha i)))))
  let Q := t.tower.norm M.det
  have hQ := t.tower.bound deg
  change Q=0 ∨ (Q.totalDegree:ℤ) ≤ 80 at hQ
  refine ⟨Q,?_,?_,?_⟩
  · rcases hQ with h|h
    · simp [h]
    · exact_mod_cast h
  · intro L _ f r hr hz
    obtain ⟨g,hg,gr⟩ := t.realizes f r hr
    have gg (z) : g (e z)=f z := DFunLike.congr_fun hg z
    have eqr : g ∘ t.root=r := funext gr
    have comp (z : Fin 4 → PP k) : g ∘ (e ∘ z)=f ∘ z := funext (fun j => gg (z j))
    have zero : g M.det=0 := by simpa only [M,map_aug_det,comp,eqr] using hz
    exact (gg Q).symm.trans (t.tower.vanishes g M.det zero)
  · intro L _ _ f hz
    obtain ⟨g,hg,zero⟩ := t.tower.liftZero f M.det hz
    have gg (z) : g (e z)=f z := DFunLike.congr_fun hg z
    have comp (z : Fin 4 → PP k) : g ∘ (e ∘ z)=f ∘ z := funext (fun j => gg (z j))
    refine ⟨g ∘ t.root,?_,?_⟩
    · intro j; simp only [Function.comp_apply,← map_pow,t.square]; exact gg _
    · simpa only [M,map_aug_det,comp] using zero

theorem four_root_eliminant (p q : PP k) (u v : Fin 4 → k)
    (b a D : Fin 4 → PP k) (hp : p.totalDegree ≤ 1) (hq : q.totalDegree ≤ 1)
    (hb : ∀ j, (b j).totalDegree ≤ 2) (ha : ∀ j, (a j).totalDegree ≤ 0)
    (hd : ∀ j, (D j).totalDegree ≤ 4) :
    let x := fun i => p+C (u i)
    let y := fun i => q+C (v i)
    ∃ Q : PP k, Q.totalDegree ≤ 80 ∧
      (∀ {L : Type u} [Field L] (f : PP k →+* L) (r : Fin 4 → L),
        (∀ j, (r j)^2=f (D j)) →
        (aug (f ∘ x) (f ∘ y) (f ∘ b) (f ∘ a) r).det=0 → f Q=0) ∧
      (∀ {L : Type u} [Field L] [IsAlgClosed L] (f : PP k →+* L), f Q=0 →
        ∃ r : Fin 4 → L, (∀ j, (r j)^2=f (D j)) ∧
          (aug (f ∘ x) (f ∘ y) (f ∘ b) (f ∘ a) r).det=0) :=
  eliminant_of_model p q u v b a D hp hq hb ha
    (formalRoots (polynomialBounds (Fin 2) k) D (fun j => polyFits (hd j)))

end
end PlanarUnitDistances.RadicalNorm
