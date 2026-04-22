import Matroid.Intersection.ExchangeGraph
import Matroid.Intersection.AugmentingPath
import Matroid.Intersection.NoShortcutPath
import Matroid.Intersection.Optimality
import Matroid.Intersection.LengthOnePath

/-!
# Matroid intersection: the min-max theorem via Edmonds-style augmenting paths

Umbrella module for the matroid intersection development. The substance is the **theorem** that
the maximum size of a common independent set equals the minimum rank-partition value
`rk_M₁(U) + rk_M₂(E \ U)` over `U ⊆ E`, proven via Edmonds' exchange-graph / augmenting-path
technique.

The proof technique is broken into:
- `Matroid.Intersection.ExchangeGraph` — exchange graph, `SourceSet`/`SinkSet`, `Terminal`,
  `TerminalCertificate`.
- `Matroid.Intersection.AugmentingPath` — `SimpleAugPath` and the minimality machinery.
- `Matroid.Intersection.NoShortcutPath` — `NoShortcutPath`, `AugmentStep`/`Run`, terminal iff,
  preservation of common independence.
- `Matroid.Intersection.Optimality` — termination (`augmentStep_wf`), `optimal_of_certificate`,
  `exists_optimal_terminal_run`.
- `Matroid.Intersection.LengthOnePath` — the smallest nontrivial augmenting step.

The actual *algorithm* (concrete BFS-based search, executable correctness) is not in this
module — it would live under `Matroid.Edmonds` once added.
-/
