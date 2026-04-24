import Mathlib.Combinatorics.Matroid.Rank.ENat

/-!
# Common independence for two matroids

Basic definitions shared across the matroid-intersection development: a set is common independent
for two matroids when it is independent in both.
-/

open Set

namespace Matroid

variable {α : Type*}

/-- A set is common independent for two matroids if it is independent in both. -/
def CommonIndep (M₁ M₂ : Matroid α) (I : Set α) : Prop :=
  M₁.Indep I ∧ M₂.Indep I

/-- The empty set is common independent for any pair of matroids on `α`. -/
theorem CommonIndep.empty (M₁ M₂ : Matroid α) : CommonIndep M₁ M₂ (∅ : Set α) :=
  ⟨M₁.empty_indep, M₂.empty_indep⟩

/-- Every common independent set is bounded above by every rank-partition value. -/
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

end Matroid
