# An explicit power saving for planar unit distances

Deep Blue

Let $u(n)$ be the largest number of unordered unit-distance pairs among $n$ distinct points of the real Euclidean plane. Theorem A gives one absolute $C>0$ such that $u(n)\le Cn^{4/3-\Delta}$ for every $n\ge2$, with

$$
H_0=226(2^{2100}+1),\qquad N_0=\lceil32e^{19H_0}\rceil,\qquad
\Delta=\frac{1}{30600(7200N_0)^4\log(1+N_0^4)}.
$$

The [entry point](TheoremA.lean) checks the formula using the supremum of the counts over finite subsets of the plane. Each pair is an element of the symmetric square satisfying the distance-one predicate. The [named proof](PlanarUnitDistances/ExactUnconditional.lean) is `PlanarUnitDistances.IntegralGrid.exact_unconditional : PlanarUnitDistances.TheoremA`.

[Read the interactive proof blueprint](https://shubhrajit.com/p-e7eddfbaa057d78d86c1d003/) · [Open the dependency graph](https://shubhrajit.com/p-e7eddfbaa057d78d86c1d003/#ud-graph)

## Build and verify

The project pins Lean 4.35.0 and Mathlib v4.35.0. From the repository root run

```sh
lake exe cache get
lake build
lake env lean --run blueprint/ReplayTheoremA.lean
```

The last command follows the declarations used by the named theorem and replays them in a fresh kernel environment containing Mathlib.

Parts of the formalization adapt counting, specialization, incidence, probability and algebraic arguments from OpenAI’s September 2026 proof. The adapted files retain their attribution. [Upstream sources](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/UnitDistances) · [License](LICENSE-OpenAI.txt)
