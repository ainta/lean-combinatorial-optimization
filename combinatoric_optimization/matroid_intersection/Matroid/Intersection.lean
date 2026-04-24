import Matroid.Intersection.ExchangeGraph
import Matroid.Intersection.AugmentingPath
import Matroid.Intersection.NoShortcutPath
import Matroid.Intersection.Optimality

/-!
# Matroid intersection: the min-max theorem via Edmonds-style augmenting paths

Umbrella module for the matroid intersection development. The substance is the **min-max
theorem**: the maximum size of a common independent set of two matroids on the same finite
ground set equals the minimum value of `rk_M₁(U) + rk_M₂(E \ U)` over `U ⊆ E`.

The headline export is `Matroid.exists_max_commonIndep_eq_min_rank_partition`.

The proof technique (Edmonds' exchange graph + augmenting paths) is broken into:
- `Matroid.Intersection.ExchangeGraph` — exchange graph, `SourceSet`/`SinkSet`, `Terminal`,
  `TerminalCertificate`.
- `Matroid.Intersection.AugmentingPath` — `SimpleAugPath` and the minimality machinery.
- `Matroid.Intersection.NoShortcutPath` — `NoShortcutPath`, `AugmentStep`/`Run`, terminal iff,
  preservation of common independence.
- `Matroid.Intersection.Optimality` — termination (`augmentStep_wf`), `optimal_of_certificate`,
  `exists_optimal_terminal_run`, `TerminalCertificate.encard_eq_rank_partition`.

The actual *algorithm* (concrete BFS-based search, executable correctness) is not in this
module — it would live under `Matroid.Edmonds` once added.
-/

open Set

namespace Matroid

variable {α : Type*}

/-- **Matroid intersection min-max theorem**.

For two matroids `M₁`, `M₂` on the same finite ground set, there exist a common independent set
`I` and a subset `U` of the ground set such that:
- `I` is a maximum common independent set,
- `U` is a minimum rank-partition (`rk M₁ U + rk M₂ (E \ U)`),
- the two values agree.

Algorithmically, `I` is reachable from `∅` by a finite run of certified augmentations through
the exchange graph, and `U` is the set of vertices that can reach a sink at termination. -/
theorem exists_max_commonIndep_eq_min_rank_partition [Finite α]
    {M₁ M₂ : Matroid α} (hE : Intersection.SameGround M₁ M₂) :
    ∃ I U,
      CommonIndep M₁ M₂ I ∧
      I.encard = M₁.eRk U + M₂.eRk (M₁.E \ U) ∧
      (∀ J, CommonIndep M₁ M₂ J → J.encard ≤ I.encard) ∧
      (∀ V, M₁.eRk U + M₂.eRk (M₁.E \ U) ≤ M₁.eRk V + M₂.eRk (M₁.E \ V)) := by
  obtain ⟨I, hRun, hTerm, hopt⟩ :=
    Intersection.exists_optimal_terminal_run hE (CommonIndep.empty M₁ M₂)
  have hI : CommonIndep M₁ M₂ I :=
    Intersection.commonIndep_of_run (CommonIndep.empty M₁ M₂) hRun
  have hcert : Intersection.TerminalCertificate M₁ M₂ I (Intersection.ReachableToSink M₁ M₂ I) :=
    Intersection.reachable_certificate hTerm
  have heq : I.encard = M₁.eRk (Intersection.ReachableToSink M₁ M₂ I) +
      M₂.eRk (M₁.E \ Intersection.ReachableToSink M₁ M₂ I) :=
    Intersection.TerminalCertificate.encard_eq_rank_partition hE hI hcert
  refine ⟨I, Intersection.ReachableToSink M₁ M₂ I, hI, heq, hopt, ?_⟩
  intro V
  rw [← heq]
  exact CommonIndep.encard_le_rank_partition hI V

end Matroid
