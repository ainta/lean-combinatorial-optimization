import Matroid.Edmonds.ExchangeGraph
import Matroid.Edmonds.AugmentingPath
import Matroid.Edmonds.NoShortcutPath
import Matroid.Edmonds.Optimality
import Matroid.Edmonds.LengthOnePath

/-!
# Edmonds' matroid-intersection algorithm

Umbrella module re-exporting the components of the abstract correctness proof:
- `Matroid.Edmonds.ExchangeGraph` — exchange graph, `SourceSet`/`SinkSet`, `Terminal`,
  `TerminalCertificate`.
- `Matroid.Edmonds.AugmentingPath` — `SimpleAugPath` and the minimality machinery.
- `Matroid.Edmonds.NoShortcutPath` — `NoShortcutPath`, `AugmentStep`/`Run`, terminal iff,
  preservation of common independence.
- `Matroid.Edmonds.Optimality` — termination (`augmentStep_wf`), `optimal_of_certificate`,
  `exists_optimal_terminal_run`.
- `Matroid.Edmonds.LengthOnePath` — the smallest nontrivial augmenting step.
-/
