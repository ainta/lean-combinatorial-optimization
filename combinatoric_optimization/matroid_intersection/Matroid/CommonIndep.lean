import Mathlib.Combinatorics.Matroid.Basic

/-!
# Common independence for two matroids

Basic definitions shared across the matroid-intersection development: a set is common independent
for two matroids when it is independent in both, and the length-one augmentation operator used by
the simplest Edmonds exchange step.
-/

open Set

namespace Matroid

variable {α : Type*}

/-- A set is common independent for two matroids if it is independent in both. -/
def CommonIndep (M₁ M₂ : Matroid α) (I : Set α) : Prop :=
  M₁.Indep I ∧ M₂.Indep I

/-- The result of augmenting `I` along the length-one alternating path
`x₀ → y → x₁`. -/
def augmentLengthOne (I : Set α) (y x₀ x₁ : α) : Set α :=
  insert x₀ (insert x₁ (I \ {y}))

end Matroid
