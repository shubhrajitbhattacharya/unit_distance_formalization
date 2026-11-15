import PlanarUnitDistances.ExactUnconditional
import Lean.Util.CollectAxioms

/-! The default build checks the conclusion against the manuscript with the
count, quantifiers, ceiling and exponent written out. The final proof has no hypotheses. -/

open Real PlanarUnitDistances
open scoped Classical

example :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      let Point := EuclideanSpace ℝ (Fin 2)
      let unit : Sym2 Point → Prop := Sym2.lift
        ⟨fun p q => dist p q = 1, fun p q => by dsimp; rw [dist_comm]⟩
      let u := sSup {m : ℕ | ∃ P : Finset Point, P.card = n ∧ (P.sym2.filter unit).card = m}
      let H₀ : ℝ := 226 * (2 ^ 2100 + 1)
      let N₀ : ℕ := ⌈32 * exp (19 * H₀)⌉₊
      (u : ℝ) ≤ C * (n : ℝ) ^
        (4 / 3 - 1 / (30600 * (7200 * (N₀ : ℝ)) ^ 4 * log (1 + (N₀ : ℝ) ^ 4))) :=
  IntegralGrid.exact_unconditional

open Lean Elab Command in
run_cmd
  let theoremName := ``IntegralGrid.exact_unconditional
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in ← collectAxioms theoremName do
    unless allowed.contains ax do
      throwError "{theoremName} depends on unexpected axiom {ax}"
