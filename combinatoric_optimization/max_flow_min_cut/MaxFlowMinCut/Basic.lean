import MaxFlowMinCut.QuiverPath
import MaxFlowMinCut.Network
import MaxFlowMinCut.CutFlow
import MaxFlowMinCut.Residual
import MaxFlowMinCut.Augment
import MaxFlowMinCut.MainTheorem

/-!
# Max-flow / min-cut

Umbrella module re-exporting the components of the max-flow / min-cut development:
- `MaxFlowMinCut.QuiverPath` — generic path-shortening helpers for `Quiver.Path`.
- `MaxFlowMinCut.Network` — `Network`, `Flow`, `IsCut`, conservation lemmas.
- `MaxFlowMinCut.CutFlow` — `outAcross`/`inAcross` decompositions and `value_le_cutCapacity`.
- `MaxFlowMinCut.Residual` — residual graph and `isMaxFlow_of_noResidualPath`.
- `MaxFlowMinCut.Augment` — augmentation along a residual path
  (`exists_better_flow_of_residualPath`).
- `MaxFlowMinCut.MainTheorem` — the max-flow / min-cut existence theorem and its variants.
-/
