import PlanarUnitDistances.QuadraticFiltration

namespace PlanarUnitDistances.RadicalNorm
noncomputable section
universe u
variable {R : Type u} [CommRing R]

/-- The formal algebra for n specified roots, together with a degree-controlled
norm. The roots specialize jointly to every prescribed tuple in every field. -/
structure RootModel (b : Bounds R) {n : ℕ} (d : Fin n → R) where
  S : Type u
  [ring : CommRing S]
  c : Bounds S
  tower : Descent b c (2^n)
  baseSmall : ∀ {m x}, b.fits m x → c.fits m (tower.incl x)
  root : Fin n → S
  square : ∀ i, (root i)^2=tower.incl (d i)
  small : ∀ i, c.fits 2 (root i)
  realizes : ∀ {L : Type u} [Field L] (f : R →+* L) (r : Fin n → L),
    (∀ i, (r i)^2=f (d i)) →
    ∃ g : S →+* L, g.comp tower.incl=f ∧ ∀ i, g (root i)=r i

attribute [instance] RootModel.ring

def noRoots (b : Bounds R) (d : Fin 0 → R) : RootModel b d where
  S := R
  c := b
  tower := trivialDescent b
  baseSmall := fun h => h
  root := Fin.elim0
  square := fun i => i.elim0
  small := fun i => i.elim0
  realizes f _ _ := ⟨f,rfl,fun i => i.elim0⟩

def addRoot {b : Bounds R} {n : ℕ} (d : Fin (n+1) → R)
    (h : b.fits 4 (d 0)) (t : RootModel b (fun i => d i.succ)) : RootModel b d := by
  let a := t.tower.incl (d 0)
  have ha : t.c.fits 4 a := t.baseSmall h
  let A := QuadraticAlgebra t.S a 0
  let emb : t.S →+* A := algebraMap t.S A
  let tower := quadraticStep t.tower a ha
  let E : Descent b (extend t.c a ha) (2^(n+1)) := by simpa only [pow_succ] using tower
  have incl : E.incl=emb.comp t.tower.incl := rfl
  refine { S := A, c := extend t.c a ha, tower := E,
           baseSmall := fun hx => ?_, root := Fin.cons QuadraticAlgebra.omega (fun i => emb (t.root i)),
           square := ?_, small := ?_, realizes := ?_ }
  · rw [incl]
    exact base_fits t.c ha (t.baseSmall hx)
  · apply Fin.cases
    · change (QuadraticAlgebra.omega : QuadraticAlgebra t.S a 0)^2 = algebraMap t.S _ a
      rw [pow_two,QuadraticAlgebra.omega_mul_omega_eq_mk]
      rfl
    · intro i
      simp only [Fin.cons_succ,← map_pow,t.square,incl,RingHom.comp_apply]
  · apply Fin.cases
    · exact root_fits t.c ha
    · intro i
      exact base_fits t.c ha (t.small i)
  · intro L _ f r hr
    obtain ⟨g,hg,gg⟩ := t.realizes f (fun i => r i.succ) (fun i => hr i.succ)
    have hroot : (r 0)^2=g a := by rw [hr]; exact (DFunLike.congr_fun hg _).symm
    let F := evalRoot g (r 0) hroot
    refine ⟨F,?_,Fin.cases ?_ (fun i => ?_)⟩
    · rw [incl,← RingHom.comp_assoc]
      exact (congrArg (fun k : t.S →+* L => k.comp t.tower.incl) (evalRoot_base g _ hroot)).trans hg
    · simp [F,evalRoot,QuadraticAlgebra.omega,Fin.cons_zero]
    · have eqg := DFunLike.congr_fun (evalRoot_base g _ hroot) (t.root i)
      exact eqg.trans (gg i)

def formalRoots (b : Bounds R) : ∀ {n} (d : Fin n → R), (∀ i, b.fits 4 (d i)) → RootModel b d
  | 0,d,_ => noRoots b d
  | _+1,d,h => addRoot d (h 0) (formalRoots b (fun i => d i.succ) (fun i => h i.succ))

end
end PlanarUnitDistances.RadicalNorm
