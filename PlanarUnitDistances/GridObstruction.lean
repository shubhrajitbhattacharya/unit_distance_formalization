import PlanarUnitDistances.CurveProduct
import PlanarUnitDistances.CurveRestriction

namespace PlanarUnitDistances.GridObstruction
open MvPolynomial Finset CurveProduct
open scoped Classical
noncomputable section
variable {k : Type*} [Field k]
abbrev Pt (k : Type*) := Fin 2 → k
abbrev Eqn (k : Type*) [Field k] := MvPolynomial (Fin 2) k

/-- The first eight slots use the left curve and the last four the right. -/
def curveAt (f g : Eqn k) (i : Fin 12) : Eqn k :=
  Fin.append (m := 8) (n := 4) (fun _ => f) (fun _ => g) i

def positions (p : Fin 8 → Pt k) (r : Fin 4 → Pt k) : Fin 12 → Pt k :=
  Fin.append p r

def upper_grids (A B : Finset (Pt k)) (E : A → B → Prop) [DecidableRel E] :=
  GridCount.grids E 8 4

/-- The separating equation bounds the number of complete actual grids,
including tuples with repetitions, by exactly 12 D E n^11. -/
theorem polynomial_grid_upper (f g : Eqn k) (hf : Irreducible f) (hg : Irreducible g)
    (A B : Finset (Pt k)) (hA : ∀ x∈A, eval x f=0) (hB : ∀ x∈B, eval x g=0)
    (edge : A → B → Prop) [DecidableRel edge] (D d n : ℕ)
    (df : f.totalDegree ≤ D) (dg : g.totalDegree ≤ D) (an : A.card ≤ n) (bn : B.card ≤ n)
    (F : MvPolynomial (Fin 12 × Fin 2) k) (hF : F.totalDegree ≤ d)
    (w : ∀ i, Curve (curveAt f g i)) (hw : eval (coords (fun i => (w i).val)) F≠0)
    (vanish : ∀ (p : Fin 8 → A) (r : Fin 4 → B), (∀ i j, edge (p i) (r j)) →
      eval (coords (positions (fun i => (p i).val) (fun j => (r j).val))) F=0) :
    (upper_grids A B edge).card ≤ 12*D*d*n^11 := by
  let C (i : Fin 12) := curveAt f g i
  let U (i : Fin 12) : Finset (Pt k) := Fin.append (m:=8) (n:=4) (fun _ => A) (fun _ => B) i
  let S (i : Fin 12) : Finset (Curve (C i)) := (U i).subtype (fun x => eval x (C i)=0)
  have ir (i : Fin 12) : Irreducible (C i) := by
    refine Fin.addCases (m:=8) (n:=4) ?_ ?_ i <;> intros <;> simp [C,curveAt,hf,hg]
  have deg (i : Fin 12) : (C i).totalDegree ≤ D := by
    refine Fin.addCases (m:=8) (n:=4) ?_ ?_ i <;> intros <;> simp [C,curveAt,df,dg]
  have size (i : Fin 12) : (S i).card ≤ n := by
    have hs : (S i).card ≤ (U i).card := by
      exact Finset.card_le_card_of_injOn Subtype.val (fun x hx => (Finset.mem_subtype.mp hx))
        Subtype.val_injective.injOn
    apply hs.trans
    refine Fin.addCases (m:=8) (n:=4) ?_ ?_ i <;> intros <;> simp [U,an,bn]
  let pos (v : (Fin 8 → A) × (Fin 4 → B)) := positions (fun i => (v.1 i).val) (fun j => (v.2 j).val)
  have onCurve (v) (i : Fin 12) : eval (pos v i) (C i)=0 := by
    refine Fin.addCases (m:=8) (n:=4) ?_ ?_ i
    · intro a
      simpa [pos,positions,C,curveAt] using hA _ (v.1 a).prop
    · intro b
      simpa [pos,positions,C,curveAt] using hB _ (v.2 b).prop
  let lift (v) (i : Fin 12) : Curve (C i) := ⟨pos v i,onCurve v i⟩
  have inj : Function.Injective lift := by
    intro u v eq
    have pairval (i : Fin 12) := congrArg Subtype.val (congrFun eq i)
    apply Prod.ext <;> funext i <;> apply Subtype.ext
    · simpa [lift,pos,positions] using pairval (Fin.castAdd 4 i)
    · simpa [lift,pos,positions] using pairval (Fin.natAdd 8 i)
  apply le_trans _ (zeros_on_product C ir F D d n deg hF S size w hw)
  apply Finset.card_le_card_of_injOn lift _ inj.injOn
  intro v hv
  apply Finset.mem_filter.mpr
  refine ⟨Fintype.mem_piFinset.mpr (fun i => ?_),vanish _ _ (Finset.mem_filter.mp hv).2⟩
  apply Finset.mem_subtype.mpr
  change pos v i ∈ U i
  refine Fin.addCases (m:=8) (n:=4) ?_ ?_ i
  · intro a
    simp [pos,positions,U]
  · intro b
    simp [pos,positions,U]


end
end PlanarUnitDistances.GridObstruction
