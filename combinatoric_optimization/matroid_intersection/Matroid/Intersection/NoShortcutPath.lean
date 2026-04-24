import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Data.Finset.Max
import Matroid.Intersection.AugmentingPath

/-!
# No-shortcut augmenting paths and certified augmentation steps

A `NoShortcutPath` is the shortest-path certificate produced from a minimal `SimpleAugPath`: it
records injectivity, disjointness, and the absence of left/right shortcuts that would let the
exchange graph collapse the path to a strictly shorter one.

This module bundles:
- the `NoShortcutPath` structure and the round-trip conversions with `SimpleAugPath`,
- the `AugmentStep` / `Run` relations driven by such certificates,
- the existence theorem turning nonterminal states into certified augmentation steps,
- the equivalence `Terminal ↔ no certified augmentation step`,
- the preservation of common independence under a no-shortcut augmentation, including the run-level
  consequence `commonIndep_of_run`.
-/

open Set

namespace Matroid.Intersection

variable {α : Type*} {M₁ M₂ : Matroid α} {I : Set α}

/-- A no-shortcut augmenting path for Edmonds' algorithm, encoded by the outside vertices
`x₀, …, xₙ` and the inside vertices `y₀, …, yₙ₋₁`. The `M₁` conditions are oriented from
left to right, while the `M₂` conditions are oriented from right to left. -/
structure NoShortcutPath (M₁ M₂ : Matroid α) (I : Set α) (n : ℕ) where
  x : Fin (n + 1) → α
  y : Fin n → α
  x_not_mem : ∀ i, x i ∉ I
  y_mem : ∀ i, y i ∈ I
  x_inj : Function.Injective x
  y_inj : Function.Injective y
  disjoint : ∀ i j, x i ≠ y j
  left_source : M₁.Indep (insert (x 0) I)
  left_not_source : ∀ i : Fin n, ¬ M₁.Indep (insert (xNext x i) I)
  left_step : ∀ i : Fin n, M₁.Indep (insert (xNext x i) (I \ {y i}))
  left_no_shortcut : ∀ ⦃i j : Fin n⦄, i < j → ¬ M₁.Indep (insert (xNext x j) (I \ {y i}))
  right_step : ∀ i : Fin n, M₂.Indep (insert (xPrev x i) (I \ {y i}))
  right_sink : M₂.Indep (insert (xLast x) I)
  right_not_sink : ∀ i : Fin n, ¬ M₂.Indep (insert (xPrev x i) I)
  right_no_shortcut : ∀ ⦃i j : Fin n⦄, i < j → ¬ M₂.Indep (insert (xPrev x i) (I \ {y j}))

/-- Forget the no-shortcut / shortest-path conditions from a certified path. -/
def NoShortcutPath.toSimpleAugPath {n : ℕ} (P : NoShortcutPath M₁ M₂ I n) :
    SimpleAugPath M₁ M₂ I n where
  x := P.x
  y := P.y
  x_not_mem := P.x_not_mem
  y_mem := P.y_mem
  left_source := P.left_source
  left_step := P.left_step
  right_step := P.right_step
  right_sink := P.right_sink

/-- A minimal explicit augmenting path satisfies the no-shortcut certificate. -/
def SimpleAugPath.toNoShortcutPath {n : ℕ}
    (P : SimpleAugPath M₁ M₂ I n) (hmin : P.Minimal) :
    NoShortcutPath M₁ M₂ I n where
  x := P.x
  y := P.y
  x_not_mem := P.x_not_mem
  y_mem := P.y_mem
  x_inj := P.x_inj_of_minimal hmin
  y_inj := P.y_inj_of_minimal hmin
  disjoint i j := by
    intro h
    exact P.x_not_mem i (h ▸ P.y_mem j)
  left_source := P.left_source
  left_not_source := P.left_not_source_of_minimal hmin
  left_step := P.left_step
  left_no_shortcut := P.left_no_shortcut_of_minimal hmin
  right_step := P.right_step
  right_sink := P.right_sink
  right_not_sink := P.right_not_sink_of_minimal hmin
  right_no_shortcut := P.right_no_shortcut_of_minimal hmin

/-- One abstract augmentation step of Edmonds' algorithm, certified by a `NoShortcutPath`. -/
def AugmentStep (M₁ M₂ : Matroid α) (I J : Set α) : Prop :=
  ∃ n, ∃ P : NoShortcutPath M₁ M₂ I n, J = augmentPath I P.x P.y

/-- A run of Edmonds-style augmentations certified by `NoShortcutPath` witnesses. -/
abbrev Run (M₁ M₂ : Matroid α) (I J : Set α) : Prop :=
  Relation.ReflTransGen (AugmentStep M₁ M₂) I J

/-- If the exchange graph is nonterminal, there is a certified no-shortcut augmenting path. -/
theorem exists_noShortcutPath_of_not_terminal
    (hNT : ¬ Terminal M₁ M₂ I) :
    ∃ n, Nonempty (NoShortcutPath M₁ M₂ I n) := by
  rcases exists_minimal_simpleAugPath_of_not_terminal hNT with ⟨n, P, hmin⟩
  exact ⟨n, ⟨P.toNoShortcutPath hmin⟩⟩

/-- Nonterminal states admit a certified augmentation step. -/
theorem exists_augmentStep_of_nonterminal
    (hNT : ¬ Terminal M₁ M₂ I) :
    ∃ J, AugmentStep M₁ M₂ I J := by
  rcases exists_noShortcutPath_of_not_terminal hNT with ⟨n, ⟨P⟩⟩
  exact ⟨augmentPath I P.x P.y, ⟨n, P, rfl⟩⟩

private theorem NoShortcutPath.source_arc {n : ℕ} (P : NoShortcutPath M₁ M₂ I n) (i : Fin n) :
    ExchangeRel M₁ M₂ I (xPrev P.x i) (P.y i) := by
  right
  refine ⟨P.x_not_mem _, ?_, P.y_mem i, P.right_step i⟩
  simpa [xPrev] using P.disjoint i.castSucc i

private theorem NoShortcutPath.sink_arc {n : ℕ} (P : NoShortcutPath M₁ M₂ I n) (i : Fin n) :
    ExchangeRel M₁ M₂ I (P.y i) (xNext P.x i) := by
  left
  refine ⟨P.y_mem i, ?_, P.x_not_mem _, P.left_step i⟩
  intro h
  exact P.disjoint i.succ i h.symm

private theorem NoShortcutPath.reaches_sink_from {n : ℕ} (P : NoShortcutPath M₁ M₂ I n)
    (m : ℕ) (hm : m ≤ n) :
    Relation.ReflTransGen (ExchangeRel M₁ M₂ I)
      (P.x ⟨m, Nat.lt_succ_of_le hm⟩) (xLast P.x) := by
  refine Nat.decreasingInduction ?_ ?_ hm
  · intro k hk hrec
    let i : Fin n := ⟨k, hk⟩
    have hxy : ExchangeRel M₁ M₂ I (P.x ⟨k, Nat.lt_succ_of_lt hk⟩) (P.y i) := by
      simpa [i, xPrev]
        using P.source_arc i
    have hyx :
        ExchangeRel M₁ M₂ I (P.y i) (P.x ⟨k + 1, Nat.succ_lt_succ hk⟩) := by
      simpa [i, xNext]
        using P.sink_arc i
    exact Relation.ReflTransGen.head hxy (Relation.ReflTransGen.head hyx hrec)
  · simpa [xLast, Fin.last] using
      (Relation.ReflTransGen.refl :
        Relation.ReflTransGen (ExchangeRel M₁ M₂ I) (P.x (Fin.last n)) (P.x (Fin.last n)))

/-- A certified no-shortcut path really does start at a source and reach a sink in the exchange
graph. -/
theorem NoShortcutPath.source_mem_reachableToSink {n : ℕ} (P : NoShortcutPath M₁ M₂ I n) :
    P.x 0 ∈ SourceSet M₁ I ∩ ReachableToSink M₁ M₂ I := by
  refine ⟨⟨P.x_not_mem 0, P.left_source⟩, ?_⟩
  refine ⟨xLast P.x, ⟨P.x_not_mem _, P.right_sink⟩, ?_⟩
  simpa using P.reaches_sink_from 0 (Nat.zero_le n)

/-- If the terminal exchange-graph condition holds, then no certified no-shortcut augmenting path
exists. -/
theorem no_noShortcutPath_of_terminal
    (hTerm : Terminal M₁ M₂ I) {n : ℕ} :
    IsEmpty (NoShortcutPath M₁ M₂ I n) := by
  refine ⟨fun P ↦ ?_⟩
  have hx : P.x 0 ∈ SourceSet M₁ I ∩ ReachableToSink M₁ M₂ I := P.source_mem_reachableToSink
  exact (Set.disjoint_left.mp hTerm hx.1) hx.2

/-- Terminal states admit no certified augmentation step. -/
theorem no_augmentStep_of_terminal
    (hTerm : Terminal M₁ M₂ I) :
    ¬ ∃ J, AugmentStep M₁ M₂ I J := by
  rintro ⟨J, n, P, rfl⟩
  exact (no_noShortcutPath_of_terminal (M₁ := M₁) (M₂ := M₂) (I := I) hTerm).false P

/-- If no certified augmentation step exists, the exchange graph is terminal. -/
theorem terminal_of_no_augmentStep
    (hNo : ¬ ∃ J, AugmentStep M₁ M₂ I J) :
    Terminal M₁ M₂ I := by
  by_contra hTerm
  exact hNo (exists_augmentStep_of_nonterminal hTerm)

/-- A state is terminal exactly when no certified augmentation step is available. -/
theorem terminal_iff_no_augmentStep :
    Terminal M₁ M₂ I ↔ ¬ ∃ J, AugmentStep M₁ M₂ I J := by
  constructor
  · exact no_augmentStep_of_terminal
  · exact terminal_of_no_augmentStep

private theorem exists_x_mem_circuit_of_subset_augmentPath
    {M : Matroid α} {C : Set α} {n : ℕ} {x : Fin (n + 1) → α} {y : Fin n → α}
    (hI : M.Indep I) (hCJ : C ⊆ augmentPath I x y) (hC : M.IsCircuit C) :
    ∃ i, x i ∈ C := by
  by_contra hnone
  have hCI : C ⊆ I := by
    intro z hz
    have hzJ := hCJ hz
    rcases hzJ with hzI | hzX
    · exact hzI.1
    · rcases hzX with ⟨i, rfl⟩
      exact False.elim (hnone ⟨i, by simpa⟩)
  exact hC.dep.not_indep (hI.subset hCI)

private theorem augmentPath_subset_ground
    {M : Matroid α} {n : ℕ} {x : Fin (n + 1) → α} {y : Fin n → α}
    (hI_ground : I ⊆ M.E) (hx_ground : ∀ i, x i ∈ M.E) :
    augmentPath I x y ⊆ M.E := by
  intro z hz
  rcases hz with hz | ⟨i, rfl⟩
  · exact hI_ground hz.1
  · exact hx_ground i

private theorem left_indep_of_noShortcut {n : ℕ}
    (hI : M₁.Indep I) (P : NoShortcutPath M₁ M₂ I n) :
    M₁.Indep (augmentPath I P.x P.y) := by
  classical
  let J : Set α := augmentPath I P.x P.y
  have hx_ground : ∀ i, P.x i ∈ M₁.E := by
    intro i
    refine Fin.cases ?_ ?_ i
    · exact P.left_source.subset_ground (by simp)
    · intro j
      simpa [xNext] using (P.left_step j).subset_ground (by simp [xNext])
  have hJ_ground : J ⊆ M₁.E := by
    exact augmentPath_subset_ground hI.subset_ground hx_ground
  by_contra hJ
  have hJ_dep : M₁.Dep J := (not_indep_iff hJ_ground).1 hJ
  obtain ⟨C, hCJ, hC⟩ := hJ_dep.exists_isCircuit_subset
  have hxC : ∃ i, P.x i ∈ C :=
    exists_x_mem_circuit_of_subset_augmentPath hI hCJ hC
  let s : Finset (Fin (n + 1)) := Finset.univ.filter fun i => P.x i ∈ C
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hxC
    exact ⟨i, by simp [s, hi]⟩
  let j : Fin (n + 1) := s.min' hs
  have hjC : P.x j ∈ C := by
    exact (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  have hjmin : ∀ {k}, P.x k ∈ C → j ≤ k := by
    intro k hk
    exact Finset.min'_le s k (by simp [s, hk])
  revert hjC hjmin
  refine Fin.cases ?_ ?_ j
  · intro hjC hjmin
    have hx0_not_closure : P.x 0 ∉ M₁.closure I := by
      have hsrc := P.left_source
      rw [hI.insert_indep_iff_of_notMem (P.x_not_mem 0)] at hsrc
      exact hsrc.2
    have hsubset : C \ {P.x 0} ⊆ M₁.closure I := by
      intro z hz
      have hzC : z ∈ C := hz.1
      have hzneq : z ≠ P.x 0 := by simpa using hz.2
      have hzJ := hCJ hzC
      rcases hzJ with hzI | hzX
      · exact M₁.subset_closure I hI.subset_ground hzI.1
      · rcases hzX with ⟨k, rfl⟩
        have hk_ne_zero : k ≠ 0 := by
          intro hk
          exact hzneq (by simp [hk])
        have hk_not_source : ¬ M₁.Indep (insert (P.x k) I) := by
          simpa [xNext] using P.left_not_source (Fin.pred k hk_ne_zero)
        have hk_not_mem : P.x k ∉ I := P.x_not_mem k
        have hk_ground : P.x k ∈ M₁.E := hx_ground k
        by_contra hk_closure
        exact hk_not_source ((hI.insert_indep_iff_of_notMem hk_not_mem).2 ⟨hk_ground, hk_closure⟩)
    exact hx0_not_closure <|
      M₁.closure_subset_closure_of_subset_closure hsubset
        (hC.mem_closure_diff_singleton_of_mem hjC)
  · intro i hjC hjmin
    have hx_not_closure : P.x i.succ ∉ M₁.closure (I \ {P.y i}) := by
      have hstep := P.left_step i
      have hdiff : M₁.Indep (I \ {P.y i}) := hI.diff _
      have hx_not_mem : P.x i.succ ∉ I \ {P.y i} := by
        simp [P.x_not_mem]
      rw [xNext, hdiff.insert_indep_iff_of_notMem hx_not_mem] at hstep
      exact hstep.2
    have hsubset : C \ {P.x i.succ} ⊆ M₁.closure (I \ {P.y i}) := by
      intro z hz
      have hzC : z ∈ C := hz.1
      have hzneq : z ≠ P.x i.succ := by simpa using hz.2
      have hzJ := hCJ hzC
      rcases hzJ with hzI | hzX
      · exact M₁.subset_closure (I \ {P.y i}) (diff_subset.trans hI.subset_ground) <| by
          refine ⟨hzI.1, ?_⟩
          intro hz_y
          exact hzI.2 ⟨i, hz_y.symm⟩
      · rcases hzX with ⟨k, rfl⟩
        have hk_ge : i.succ ≤ k := hjmin (by simpa using hzC)
        have hk_ne : k ≠ i.succ := by
          intro hk
          exact hzneq (by simp [hk])
        have hk_gt : i.succ < k := lt_of_le_of_ne hk_ge hk_ne.symm
        have hk_ne_zero : k ≠ 0 := by
          intro hk
          subst k
          simp at hk_gt
        have hshortcut : ¬ M₁.Indep (insert (P.x k) (I \ {P.y i})) := by
          have hik : i < Fin.pred k hk_ne_zero := (Fin.lt_pred_iff hk_ne_zero).2 hk_gt
          simpa [xNext] using P.left_no_shortcut hik
        have hk_not_mem : P.x k ∉ I \ {P.y i} := by
          simp [P.x_not_mem]
        have hk_ground : P.x k ∈ M₁.E := hx_ground k
        have hdiff : M₁.Indep (I \ {P.y i}) := hI.diff _
        by_contra hk_closure
        exact hshortcut ((hdiff.insert_indep_iff_of_notMem hk_not_mem).2 ⟨hk_ground, hk_closure⟩)
    exact hx_not_closure <|
      M₁.closure_subset_closure_of_subset_closure hsubset
        (hC.mem_closure_diff_singleton_of_mem hjC)

private theorem right_indep_of_noShortcut {n : ℕ}
    (hI : M₂.Indep I) (P : NoShortcutPath M₁ M₂ I n) :
    M₂.Indep (augmentPath I P.x P.y) := by
  classical
  let J : Set α := augmentPath I P.x P.y
  have hx_ground : ∀ i, P.x i ∈ M₂.E := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa [xLast] using P.right_sink.subset_ground (by simp [xLast])
    · intro j
      simpa [xPrev] using (P.right_step j).subset_ground (by simp [xPrev])
  have hJ_ground : J ⊆ M₂.E := by
    exact augmentPath_subset_ground hI.subset_ground hx_ground
  by_contra hJ
  have hJ_dep : M₂.Dep J := (not_indep_iff hJ_ground).1 hJ
  obtain ⟨C, hCJ, hC⟩ := hJ_dep.exists_isCircuit_subset
  have hxC : ∃ i, P.x i ∈ C :=
    exists_x_mem_circuit_of_subset_augmentPath hI hCJ hC
  let s : Finset (Fin (n + 1)) := Finset.univ.filter fun i => P.x i ∈ C
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hxC
    exact ⟨i, by simp [s, hi]⟩
  let j : Fin (n + 1) := s.max' hs
  have hjC : P.x j ∈ C := by
    exact (Finset.mem_filter.mp (Finset.max'_mem s hs)).2
  have hjmax : ∀ {k}, P.x k ∈ C → k ≤ j := by
    intro k hk
    exact Finset.le_max' s k (by simp [s, hk])
  revert hjC hjmax
  refine Fin.lastCases ?_ ?_ j
  · intro hjC hjmax
    have hxlast_not_closure : xLast P.x ∉ M₂.closure I := by
      have hsink := P.right_sink
      rw [xLast, hI.insert_indep_iff_of_notMem (P.x_not_mem _)] at hsink
      exact hsink.2
    have hsubset : C \ {xLast P.x} ⊆ M₂.closure I := by
      intro z hz
      have hzC : z ∈ C := hz.1
      have hzneq : z ≠ xLast P.x := by simpa [xLast] using hz.2
      have hzJ := hCJ hzC
      rcases hzJ with hzI | hzX
      · exact M₂.subset_closure I hI.subset_ground hzI.1
      · rcases hzX with ⟨k, rfl⟩
        cases k using Fin.lastCases with
        | last =>
            exfalso
            exact hzneq rfl
        | cast k =>
            have hk_not_sink : ¬ M₂.Indep (insert (P.x k.castSucc) I) := P.right_not_sink k
            have hk_not_mem : P.x k.castSucc ∉ I := P.x_not_mem _
            have hk_ground : P.x k.castSucc ∈ M₂.E := hx_ground _
            by_contra hk_closure
            exact hk_not_sink ((hI.insert_indep_iff_of_notMem hk_not_mem).2 ⟨hk_ground, hk_closure⟩)
    exact hxlast_not_closure <|
      M₂.closure_subset_closure_of_subset_closure hsubset
        (hC.mem_closure_diff_singleton_of_mem hjC)
  · intro i hjC hjmax
    have hx_not_closure : xPrev P.x i ∉ M₂.closure (I \ {P.y i}) := by
      have hstep := P.right_step i
      have hdiff : M₂.Indep (I \ {P.y i}) := hI.diff _
      have hx_not_mem : xPrev P.x i ∉ I \ {P.y i} := by
        simp [xPrev, P.x_not_mem]
      have hstep' : M₂.Indep (insert (xPrev P.x i) (I \ {P.y i})) := by
        simpa [xPrev] using hstep
      rw [hdiff.insert_indep_iff_of_notMem hx_not_mem] at hstep'
      exact hstep'.2
    have hsubset : C \ {xPrev P.x i} ⊆ M₂.closure (I \ {P.y i}) := by
      intro z hz
      have hzC : z ∈ C := hz.1
      have hzneq : z ≠ xPrev P.x i := by simpa [xPrev] using hz.2
      have hzJ := hCJ hzC
      rcases hzJ with hzI | hzX
      · exact M₂.subset_closure (I \ {P.y i}) (diff_subset.trans hI.subset_ground) <| by
          refine ⟨hzI.1, ?_⟩
          intro hz_y
          exact hzI.2 ⟨i, hz_y.symm⟩
      · rcases hzX with ⟨k, rfl⟩
        have hk_le : k ≤ i.castSucc := hjmax (by simpa using hzC)
        have hk_ne : k ≠ i.castSucc := by
          intro hk
          exact hzneq (by simp [xPrev, hk])
        have hk_lt : k < i.castSucc := lt_of_le_of_ne hk_le hk_ne
        cases k using Fin.lastCases with
        | last =>
            exfalso
            exact not_lt_of_ge (Fin.le_last _) hk_lt
        | cast k =>
            have hk_lt' : k < i := by simpa using hk_lt
            have hshortcut : ¬ M₂.Indep (insert (P.x k.castSucc) (I \ {P.y i})) := by
              simpa [xPrev] using P.right_no_shortcut hk_lt'
            have hk_not_mem : P.x k.castSucc ∉ I \ {P.y i} := by
              simp [P.x_not_mem]
            have hk_ground : P.x k.castSucc ∈ M₂.E := hx_ground _
            have hdiff : M₂.Indep (I \ {P.y i}) := hI.diff _
            by_contra hk_closure
            exact hshortcut <|
              (hdiff.insert_indep_iff_of_notMem hk_not_mem).2 ⟨hk_ground, hk_closure⟩
    exact hx_not_closure <|
      M₂.closure_subset_closure_of_subset_closure hsubset
        (hC.mem_closure_diff_singleton_of_mem hjC)

/-- Augmenting along a no-shortcut path preserves common independence. -/
theorem NoShortcutPath.commonIndep_augment {n : ℕ}
    (hI : CommonIndep M₁ M₂ I) (P : NoShortcutPath M₁ M₂ I n) :
    CommonIndep M₁ M₂ (augmentPath I P.x P.y) := by
  exact ⟨left_indep_of_noShortcut hI.1 P, right_indep_of_noShortcut hI.2 P⟩

/-- A certified augmentation step preserves common independence. -/
theorem augmentStep_commonIndep {I J : Set α}
    (hI : CommonIndep M₁ M₂ I) (hStep : AugmentStep M₁ M₂ I J) :
    CommonIndep M₁ M₂ J := by
  rcases hStep with ⟨n, P, rfl⟩
  exact P.commonIndep_augment hI

/-- Common independence is preserved along any certified augmentation run. -/
theorem commonIndep_of_run {I₀ I : Set α}
    (h₀ : CommonIndep M₁ M₂ I₀) (hRun : Run M₁ M₂ I₀ I) :
    CommonIndep M₁ M₂ I := by
  induction hRun with
  | refl =>
      exact h₀
  | @tail K L hRun hStep ih =>
      exact augmentStep_commonIndep ih hStep

end Matroid.Intersection
