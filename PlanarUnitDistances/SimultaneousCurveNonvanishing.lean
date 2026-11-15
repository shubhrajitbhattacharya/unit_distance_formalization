import PlanarUnitDistances.CurveProduct
import PlanarUnitDistances.InfiniteAbscissas

namespace PlanarUnitDistances.Competition.GenericCurvePoint
open Finset MvPolynomial CurveProduct
open scoped Classical
noncomputable section

private theorem curve_sample {b : Poly₂} (irr : Irreducible b)
    (two : ∃p r : Fin 2 → ℂ,eval p b=0 ∧ eval r b=0 ∧ p 0≠r 0) (n : ℕ) :
    ∃ S : Finset (Curve b),S.card=n := by
  have inf := infinite_abscissas irr two
  choose row zero first using (fun a : abscissas b => a.prop)
  let lift : abscissas b ↪ Curve b := ⟨fun a => ⟨row a,zero a⟩,by
    intro a c eq
    apply Subtype.ext
    exact (first a).symm.trans ((congrArg (fun x : Curve b => x.val 0) eq).trans (first c))⟩
  exact ⟨((range n).map (inf.natEmbedding _)).map lift,by simp⟩

private theorem avoid_two_on_product (B : Fin 12 → Poly₂) (irr : ∀i,Irreducible (B i))
    (D : ℕ) (degree : ∀i,(B i).totalDegree≤D)
    (sample : ∀n i,∃S : Finset (Curve (B i)),S.card=n) (F G : MvPolynomial (Fin 12 × Fin 2) ℂ)
    (f : ∃w : ∀i,Curve (B i),eval (coords fun i => (w i).val) F≠0)
    (g : ∃w : ∀i,Curve (B i),eval (coords fun i => (w i).val) G≠0) :
    ∃w : ∀i,Curve (B i),eval (coords fun i => (w i).val) (F*G)≠0 := by
  let N := 12*D*(F.totalDegree+G.totalDegree)+1
  choose S size using sample N
  let grid := Fintype.piFinset S
  let bad (H : MvPolynomial (Fin 12 × Fin 2) ℂ) :=
    grid.filter fun w => eval (coords fun i => (w i).val) H=0
  have count : grid.card=N^12 := by
    change (Fintype.piFinset S).card=_
    rw [Fintype.card_piFinset]
    simp [size]
  obtain ⟨w,fw⟩ := f
  obtain ⟨v,gv⟩ := g
  have bF := zeros_on_product B irr F D F.totalDegree N degree le_rfl S (fun i => (size i).le) w fw
  have bG := zeros_on_product B irr G D G.totalDegree N degree le_rfl S (fun i => (size i).le) v gv
  by_contra! zero
  have cover : grid ⊆ bad F ∪ bad G := by
    intro x mem
    have z : eval (coords fun i => (x i).val) F=0 ∨ eval (coords fun i => (x i).val) G=0 :=
      mul_eq_zero.mp (by simpa only [map_mul] using zero x)
    rcases z with z|z
    · exact mem_union_left _ (mem_filter.mpr ⟨mem,z⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem,z⟩)
  have cap := (card_le_card cover).trans ((card_union_le ..).trans (Nat.add_le_add bF bG))
  rw [count] at cap
  change N^12 ≤ 12*D*F.totalDegree*N^11+12*D*G.totalDegree*N^11 at cap
  have strict : 12*D*(F.totalDegree+G.totalDegree)*N^11<N^12 := calc
    _ < N*N^11 := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (pow_pos (Nat.succ_pos _) _)
    _ = _ := by ring
  exact strict.not_ge (by rw [Nat.mul_add,Nat.add_mul]; exact cap)

/-- Two nonvanishing witnesses on the original twelve-curve product give
one simultaneous witness. A polynomial of either factor may vanish on
the witness supplied for the other. -/
theorem nonzero_product_on_curves {f g : Poly₂} (pair : CurvePair f g) {F G : MvPolynomial Coord ℂ}
    (hF : ∃ x∈curveProduct f g,eval x F≠0) (hG : ∃ x∈curveProduct f g,eval x G≠0) :
    ∃ x∈curveProduct f g,eval x (F*G)≠0 := by
  let e : Slot ≃ Fin 12 := finSumFinEquiv
  let h (s : Slot) : Poly₂ := s.elim (fun _ => f) (fun _ => g)
  let B (i : Fin 12) := h (e.symm i)
  have either (s : Slot) : h s=f ∨ h s=g := by cases s <;> simp [h]
  have irr (i : Fin 12) := (pair.1 (B i) (either _)).1
  have degree (i : Fin 12) : (B i).totalDegree ≤ max f.totalDegree g.totalDegree := by
    rcases either (e.symm i) with eq|eq
    · exact (congrArg totalDegree eq).trans_le (le_max_left ..)
    · exact (congrArg totalDegree eq).trans_le (le_max_right ..)
  have sample (n i) := curve_sample (irr i) ((pair.1 (B i) (either _)).2.2 0) n
  let index (b : Coord) : Fin 12 × Fin 2 := (e b.1,b.2)
  let flat (w : ∀i,Curve (B i)) : GridTuple := fun b => (w (e b.1)).val b.2
  have on (x : GridTuple) (hx : x∈curveProduct f g) (s : Slot) : eval (fun d => x (s,d)) (h s)=0 := by
    cases s with
    | inl i => exact hx.1 i
    | inr j => exact hx.2 j
  let lift (x : GridTuple) (hx : x∈curveProduct f g) (i : Fin 12) : Curve (B i) :=
    ⟨fun d => x (e.symm i,d),on x hx _⟩
  have flat_lift (x : GridTuple) (hx : x∈curveProduct f g) : flat (lift x hx)=x := by
    funext b
    simp [flat,lift]
  have ev (w : ∀i,Curve (B i)) (H : MvPolynomial Coord ℂ) :
      eval (coords fun i => (w i).val) (rename index H)=eval (flat w) H := by
    rw [eval_rename]; rfl
  have witness (H : MvPolynomial Coord ℂ) (hw : ∃x∈curveProduct f g,eval x H≠0) :
      ∃w : ∀i,Curve (B i),eval (coords fun i => (w i).val) (rename index H)≠0 := by
    obtain ⟨x,hx,nz⟩ := hw
    exact ⟨lift x hx,by rwa [ev,flat_lift]⟩
  obtain ⟨w,nz⟩ := avoid_two_on_product B irr _ degree sample _ _ (witness F hF) (witness G hG)
  have eq (s : Slot) : eval (fun d => flat w (s,d)) (h s)=0 := by
    simpa only [flat,B,Equiv.symm_apply_apply] using (w (e s)).prop
  refine ⟨flat w,⟨fun i => eq (.inl i),fun j => eq (.inr j)⟩,?_⟩
  rw [←map_mul] at nz
  rwa [ev] at nz


end
end PlanarUnitDistances.Competition.GenericCurvePoint
