import Matroid.Intersection

/-!
# Algorithm spec: search procedures for matroid intersection

A `SearchSpec` is the abstract interface that any concrete matroid-intersection algorithm must
satisfy: given a current common independent set, it either returns an augmenting step or proves
the state is terminal. By `Matroid.Intersection.terminal_iff_no_augmentStep` these are the only
two possibilities, so a `SearchSpec` is a *constructive choice* of which one to take.

This module provides:
- the `SearchSpec` structure;
- `SearchSpec.classical`, a noncomputable witness produced by classical choice over the existing
  existence theorem `exists_augmentStep_of_nonterminal`.

Concrete computable implementations (e.g. BFS on the exchange graph) live downstream and
provide their own `SearchSpec` instances under additional decidability assumptions.
-/

namespace Matroid.Edmonds

variable {α : Type*} {M₁ M₂ : Matroid α}

/-- The result of one step of a search: either a certified augmenting step with target set
`J`, or a proof that the current state `I` is terminal. -/
inductive SearchResult (M₁ M₂ : Matroid α) (I : Set α) : Type _ where
  | step (J : Set α) (h : Intersection.AugmentStep M₁ M₂ I J) : SearchResult M₁ M₂ I
  | terminal (h : Intersection.Terminal M₁ M₂ I) : SearchResult M₁ M₂ I

/-- A search procedure for matroid intersection: given a common independent set `I`, return a
`SearchResult`. -/
structure SearchSpec (M₁ M₂ : Matroid α) where
  search : (I : Set α) → CommonIndep M₁ M₂ I → SearchResult M₁ M₂ I

namespace SearchSpec

/-- A noncomputable witness that a `SearchSpec` exists for every matroid pair, by classical
choice over `exists_augmentStep_of_nonterminal`. Layer 3 will provide computable
implementations under additional decidability assumptions. -/
noncomputable def classical (M₁ M₂ : Matroid α) : SearchSpec M₁ M₂ where
  search I _ := by
    classical
    by_cases hT : Intersection.Terminal M₁ M₂ I
    · exact SearchResult.terminal hT
    · have h := Intersection.exists_augmentStep_of_nonterminal hT
      exact SearchResult.step h.choose h.choose_spec

end SearchSpec

end Matroid.Edmonds
