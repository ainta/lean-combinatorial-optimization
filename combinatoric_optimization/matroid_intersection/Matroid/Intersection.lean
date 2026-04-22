import Matroid.Intersection.ExchangeGraph
import Matroid.Intersection.AugmentingPath
import Matroid.Intersection.NoShortcutPath
import Matroid.Intersection.Optimality
import Matroid.Intersection.LengthOnePath

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
- `Matroid.Intersection.LengthOnePath` — the smallest nontrivial augmenting step.

The actual *algorithm* (concrete BFS-based search, executable correctness) is not in this
module — it would live under `Matroid.Edmonds` once added.
-/

open Set

namespace Matroid

variable {α : Type*}

/-- The empty set is common independent for any pair of matroids on `α`. -/
theorem CommonIndep.empty (M₁ M₂ : Matroid α) : CommonIndep M₁ M₂ (∅ : Set α) :=
  ⟨M₁.empty_indep, M₂.empty_indep⟩

/-- The matroid-intersection inequality: every common independent set is bounded above by every
rank-partition value `rk M₁ U + rk M₂ (E \ U)`. This is the easy direction; the matching
existence of a witness is `exists_max_commonIndep_eq_min_rank_partition`. -/
theorem CommonIndep.encard_le_rank_partition {M₁ M₂ : Matroid α} {J : Set α}
    (hJ : CommonIndep M₁ M₂ J) (U : Set α) :
    J.encard ≤ M₁.eRk U + M₂.eRk (M₁.E \ U) := by
  have hJ_left : M₁.Indep (J ∩ U) := hJ.1.subset inter_subset_left
  have hJ_right : M₂.Indep (J ∩ (M₁.E \ U)) := hJ.2.subset inter_subset_left
  have hJ_partition : J = (J ∩ U) ∪ (J ∩ (M₁.E \ U)) := by
    ext z
    constructor
    · intro hzJ
      by_cases hzU : z ∈ U
      · exact Or.inl ⟨hzJ, hzU⟩
      · exact Or.inr ⟨hzJ, hJ.1.subset_ground hzJ, hzU⟩
    · rintro (⟨hzJ, _⟩ | ⟨hzJ, _, _⟩) <;> exact hzJ
  have hJ_disj : Disjoint (J ∩ U) (J ∩ (M₁.E \ U)) := by
    refine disjoint_left.2 ?_
    intro z hzL hzR
    exact hzR.2.2 hzL.2
  calc
    J.encard = ((J ∩ U) ∪ (J ∩ (M₁.E \ U))).encard := congrArg Set.encard hJ_partition
    _ = (J ∩ U).encard + (J ∩ (M₁.E \ U)).encard := by rw [Set.encard_union_eq hJ_disj]
    _ ≤ M₁.eRk U + M₂.eRk (M₁.E \ U) := by
      gcongr
      · exact hJ_left.encard_le_eRk_of_subset inter_subset_right
      · exact hJ_right.encard_le_eRk_of_subset inter_subset_right

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
