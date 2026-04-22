import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Data.Set.Card
import Matroid.CommonIndep

/-!
# Length-one augmenting paths

The smallest nontrivial augmenting step in Edmonds' algorithm: a single inside vertex `y` is
swapped out, an outside source `x₀` enters via `M₁`, and an outside sink `x₁` enters via `M₂`.
Soundness (`commonIndep_augment`) and the cardinality bookkeeping (`ncard_augment`) are stated
independently of the general `NoShortcutPath` machinery.
-/

open Set

namespace Matroid.Edmonds

variable {α : Type*} {M₁ M₂ : Matroid α} {I : Set α} {y x₀ x₁ : α}

/-- Data for the smallest nontrivial augmenting path in Edmonds' algorithm:
`x₀ → y → x₁`, where `x₀` is a source for `M₁`, `x₁` is a sink for `M₂`,
and the two diagonal exchanges are valid. -/
structure LengthOnePath (M₁ M₂ : Matroid α) (I : Set α) (y x₀ x₁ : α) : Prop where
  y_mem : y ∈ I
  x₀_not_mem : x₀ ∉ I
  x₁_not_mem : x₁ ∉ I
  x_ne : x₀ ≠ x₁
  left_source : M₁.Indep (insert x₀ I)
  left_step : M₁.Indep (insert x₁ (I \ {y}))
  left_internal_span : x₁ ∈ M₁.closure I
  right_step : M₂.Indep (insert x₀ (I \ {y}))
  right_sink : M₂.Indep (insert x₁ I)
  right_internal_span : x₀ ∈ M₂.closure I

/-- Soundness of the smallest nontrivial augmenting step in Edmonds' algorithm. -/
theorem LengthOnePath.commonIndep_augment
    (hI : CommonIndep M₁ M₂ I) (P : LengthOnePath M₁ M₂ I y x₀ x₁) :
    CommonIndep M₁ M₂ (augmentLengthOne I y x₀ x₁) := by
  constructor
  · have hsource_not_closure : x₀ ∉ M₁.closure I := by
      have hsrc := P.left_source
      rw [hI.1.insert_indep_iff_of_notMem P.x₀_not_mem] at hsrc
      exact hsrc.2
    have hstep_subset : insert x₁ (I \ {y}) ⊆ M₁.closure I := by
      refine insert_subset P.left_internal_span ?_
      exact diff_subset.trans (M₁.subset_closure I hI.1.subset_ground)
    have hsource_not_closure_step : x₀ ∉ M₁.closure (insert x₁ (I \ {y})) :=
      fun hx => hsource_not_closure <| by
        simpa [M₁.closure_closure I] using M₁.closure_subset_closure hstep_subset hx
    have hsource_not_mem_step : x₀ ∉ insert x₁ (I \ {y}) := by
      simp [P.x_ne, P.x₀_not_mem]
    rw [augmentLengthOne]
    rw [P.left_step.insert_indep_iff_of_notMem hsource_not_mem_step]
    exact ⟨P.left_source.subset_ground (by simp), hsource_not_closure_step⟩
  · have hsink_not_closure : x₁ ∉ M₂.closure I := by
      have hsink := P.right_sink
      rw [hI.2.insert_indep_iff_of_notMem P.x₁_not_mem] at hsink
      exact hsink.2
    have hstep_subset : insert x₀ (I \ {y}) ⊆ M₂.closure I := by
      refine insert_subset P.right_internal_span ?_
      exact diff_subset.trans (M₂.subset_closure I hI.2.subset_ground)
    have hsink_not_closure_step : x₁ ∉ M₂.closure (insert x₀ (I \ {y})) :=
      fun hx => hsink_not_closure <| by
        simpa [M₂.closure_closure I] using M₂.closure_subset_closure hstep_subset hx
    have hsink_not_mem_step : x₁ ∉ insert x₀ (I \ {y}) := by
      simp [P.x_ne.symm, P.x₁_not_mem]
    rw [augmentLengthOne]
    rw [insert_comm, P.right_step.insert_indep_iff_of_notMem hsink_not_mem_step]
    exact ⟨P.right_sink.subset_ground (by simp), hsink_not_closure_step⟩

section Cardinality

variable [Finite α]

/-- A length-one augmenting step increases the cardinality of the common independent set by
one. -/
theorem LengthOnePath.ncard_augment
    (P : LengthOnePath M₁ M₂ I y x₀ x₁) :
    (augmentLengthOne I y x₀ x₁).ncard = I.ncard + 1 := by
  classical
  rw [augmentLengthOne]
  have hy_diff : y ∉ I \ {y} := by simp
  have hx₁_diff : x₁ ∉ I \ {y} := by
    intro hx
    exact P.x₁_not_mem hx.1
  have hx₀_mid : x₀ ∉ insert x₁ (I \ {y}) := by
    simp [P.x_ne, P.x₀_not_mem]
  rw [Set.ncard_insert_of_notMem hx₀_mid, Set.ncard_insert_of_notMem hx₁_diff,
    Set.ncard_diff_singleton_of_mem P.y_mem]
  have hycard := Set.ncard_diff_singleton_add_one (s := I) P.y_mem
  omega

end Cardinality

end Matroid.Edmonds
