import Matroid.Edmonds.Search

/-!
# Algorithm correctness from a search specification

Given any `SearchSpec`, this module builds the iterative procedure that repeatedly calls the
search and augments the current common independent set, and proves the standard correctness
properties:

- termination: the procedure halts at a terminal state (`SearchSpec.iterate_terminal`);
- soundness: the trace is an `Intersection.Run` of certified augmentation steps, so the result
  is still common independent (`SearchSpec.iterate_run`, `SearchSpec.iterate_commonIndep`);
- optimality: the result is a maximum common independent set, and witnesses the matroid-
  intersection min-max theorem in algorithmic form (`SearchSpec.iterate_optimal`,
  `SearchSpec.iterate_max_eq_min_rank_partition`).

Termination is by `Intersection.augmentStep_wf` — each augmentation strictly increases
cardinality, and the ground set is finite. The bundled subtype `iterateBundled` performs the
well-founded recursion once and projects out the result, terminal proof, and run trace.
-/

namespace Matroid.Edmonds

open Matroid.Intersection

variable {α : Type*} [Finite α] {M₁ M₂ : Matroid α}

/-- The iterative procedure bundled with proofs of termination and reachability. -/
noncomputable def SearchSpec.iterateBundled (S : SearchSpec M₁ M₂) :
    (I : Set α) → CommonIndep M₁ M₂ I →
    { J : Set α // Terminal M₁ M₂ J ∧ Run M₁ M₂ I J } :=
  WellFounded.fix augmentStep_wf
    (fun I ih hI =>
      match S.search I hI with
      | SearchResult.terminal hT => ⟨I, hT, Relation.ReflTransGen.refl⟩
      | SearchResult.step J hStep =>
          let h := ih J hStep (augmentStep_commonIndep hI hStep)
          ⟨h.val, h.prop.1, Relation.ReflTransGen.head hStep h.prop.2⟩)

/-- The iterative procedure: starting from `I`, repeatedly call the search and augment until
the search returns `Terminal`. -/
noncomputable def SearchSpec.iterate (S : SearchSpec M₁ M₂)
    (I : Set α) (hI : CommonIndep M₁ M₂ I) : Set α :=
  (S.iterateBundled I hI).val

/-- The iterator stops at a terminal state. -/
theorem SearchSpec.iterate_terminal (S : SearchSpec M₁ M₂)
    (I : Set α) (hI : CommonIndep M₁ M₂ I) :
    Terminal M₁ M₂ (S.iterate I hI) :=
  (S.iterateBundled I hI).prop.1

/-- The iterator's trace is an `Intersection.Run`. -/
theorem SearchSpec.iterate_run (S : SearchSpec M₁ M₂)
    (I : Set α) (hI : CommonIndep M₁ M₂ I) :
    Run M₁ M₂ I (S.iterate I hI) :=
  (S.iterateBundled I hI).prop.2

/-- The iterator preserves common independence. -/
theorem SearchSpec.iterate_commonIndep (S : SearchSpec M₁ M₂)
    (I : Set α) (hI : CommonIndep M₁ M₂ I) :
    CommonIndep M₁ M₂ (S.iterate I hI) :=
  commonIndep_of_run hI (S.iterate_run I hI)

/-- **Algorithm correctness**: any `SearchSpec`, iterated from any common independent set,
produces a maximum common independent set. -/
theorem SearchSpec.iterate_optimal (S : SearchSpec M₁ M₂)
    (hE : SameGround M₁ M₂) (I : Set α) (hI : CommonIndep M₁ M₂ I) :
    ∀ J, CommonIndep M₁ M₂ J → J.encard ≤ (S.iterate I hI).encard :=
  run_correct hE hI (S.iterate_run I hI) (S.iterate_terminal I hI)

/-- **Algorithmic min-max**: starting from `∅`, iterating any `SearchSpec` yields a witness
pair `(I, U)` of a maximum common independent set and a min rank-partition. This is the
algorithmic version of `Matroid.exists_max_commonIndep_eq_min_rank_partition`. -/
theorem SearchSpec.iterate_max_eq_min_rank_partition (S : SearchSpec M₁ M₂)
    (hE : SameGround M₁ M₂) :
    let I := S.iterate ∅ (CommonIndep.empty M₁ M₂)
    let U := ReachableToSink M₁ M₂ I
    CommonIndep M₁ M₂ I ∧
    I.encard = M₁.eRk U + M₂.eRk (M₁.E \ U) ∧
    (∀ J, CommonIndep M₁ M₂ J → J.encard ≤ I.encard) ∧
    (∀ V, M₁.eRk U + M₂.eRk (M₁.E \ U) ≤ M₁.eRk V + M₂.eRk (M₁.E \ V)) := by
  intro I U
  have h₀ : CommonIndep M₁ M₂ (∅ : Set α) := CommonIndep.empty M₁ M₂
  have hI : CommonIndep M₁ M₂ I := S.iterate_commonIndep ∅ h₀
  have hTerm : Terminal M₁ M₂ I := S.iterate_terminal ∅ h₀
  have hcert : TerminalCertificate M₁ M₂ I U := reachable_certificate hTerm
  have heq : I.encard = M₁.eRk U + M₂.eRk (M₁.E \ U) :=
    TerminalCertificate.encard_eq_rank_partition hE hI hcert
  refine ⟨hI, heq, S.iterate_optimal hE ∅ h₀, ?_⟩
  intro V
  rw [← heq]
  exact CommonIndep.encard_le_rank_partition hI V

end Matroid.Edmonds
