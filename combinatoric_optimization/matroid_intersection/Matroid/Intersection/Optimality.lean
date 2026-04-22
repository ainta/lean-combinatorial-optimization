import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Set.Card
import Matroid.Intersection.NoShortcutPath

/-!
# Termination and optimality of Edmonds' algorithm

In the finite setting:
- each certified augmentation strictly increases the cardinality of the current common independent
  set, so the augmentation step relation is well-founded;
- the reachable-to-sink set is a `TerminalCertificate` whenever the exchange-graph terminal
  condition holds;
- the certificate gives a min-max optimality argument bounding any common independent set.

Putting these together, repeated certified augmentation reaches an optimal common independent set
in finitely many steps (`exists_optimal_terminal_run`).
-/

open Set

namespace Matroid.Intersection

variable {α : Type*} {M₁ M₂ : Matroid α} {I : Set α}

section NoShortcutCardinality

variable [Finite α]

/-- A no-shortcut augmenting path increases the size of the current common independent set by
one. -/
theorem NoShortcutPath.ncard_augment {n : ℕ} (P : NoShortcutPath M₁ M₂ I n) :
    (augmentPath I P.x P.y).ncard = I.ncard + 1 := by
  classical
  have hy_subset : Set.range P.y ⊆ I := by
    rintro _ ⟨i, rfl⟩
    exact P.y_mem i
  have hdisj : Disjoint (I \ Set.range P.y) (Set.range P.x) := by
    refine disjoint_left.2 ?_
    intro z hzI hzX
    rcases hzX with ⟨i, rfl⟩
    exact P.x_not_mem i hzI.1
  have hy_card : (Set.range P.y).ncard = n := by
    simpa using Set.ncard_range_of_injective P.y_inj
  have hx_card : (Set.range P.x).ncard = n + 1 := by
    simpa using Set.ncard_range_of_injective P.x_inj
  have hdiff : (I \ Set.range P.y).ncard = I.ncard - n := by
    simpa [hy_card] using Set.ncard_diff hy_subset
  have hy_le : n ≤ I.ncard := by
    rw [← hy_card]
    exact Set.ncard_le_ncard hy_subset
  calc
    (augmentPath I P.x P.y).ncard = (I \ Set.range P.y).ncard + (Set.range P.x).ncard := by
      rw [augmentPath, Set.ncard_union_eq hdisj]
    _ = (I.ncard - n) + (n + 1) := by rw [hdiff, hx_card]
    _ = I.ncard + 1 := by rw [← Nat.add_assoc, Nat.sub_add_cancel hy_le]

/-- A certified augmentation step increases the current set size by one. -/
theorem augmentStep_ncard {I J : Set α}
    (hStep : AugmentStep M₁ M₂ I J) :
    J.ncard = I.ncard + 1 := by
  rcases hStep with ⟨n, P, rfl⟩
  exact P.ncard_augment

/-- Certified augmentation cannot continue forever: the reverse step relation is well-founded
because each step strictly increases cardinality. -/
theorem augmentStep_wf : WellFounded (flip (AugmentStep M₁ M₂)) := by
  let _ := Fintype.ofFinite α
  refine
    Subrelation.wf
      (r := (measure fun I : Set α => Fintype.card α - I.ncard).rel)
      ?_ ((measure fun I : Set α => Fintype.card α - I.ncard).wf)
  intro A B hStep
  change Fintype.card α - A.ncard < Fintype.card α - B.ncard
  have hcard : A.ncard = B.ncard + 1 := augmentStep_ncard hStep
  have hA_le : A.ncard ≤ Fintype.card α := by
    simpa using Set.ncard_le_ncard (s := A) (t := Set.univ) (by intro x hx; simp)
  omega

end NoShortcutCardinality

section TerminalOptimality

variable {U J : Set α}

private theorem left_rank_eq_of_certificate [Finite α]
    (_hE : SameGround M₁ M₂) (hI : CommonIndep M₁ M₂ I)
    (hU : TerminalCertificate M₁ M₂ I U) :
    M₁.eRk U = (I ∩ U).encard := by
  have hIU_indep : M₁.Indep (I ∩ U) := hI.1.subset inter_subset_left
  apply le_antisymm
  · by_contra hlt
    have hlt' : M₁.eRk (I ∩ U) < M₁.eRk U := by
      have hlt' : (I ∩ U).encard < M₁.eRk U := lt_of_not_ge hlt
      rwa [← hIU_indep.eRk_eq_encard] at hlt'
    obtain ⟨x, hxU, hxrank⟩ := M₁.exists_eRk_insert_eq_add_one_of_lt hlt'
    have hx_mem_U : x ∈ U := hxU.1
    have hx_not_mem_IU : x ∉ I ∩ U := hxU.2
    have hx_not_mem_I : x ∉ I := by
      intro hxI
      exact hxU.2 ⟨hxI, hxU.1⟩
    have hx_insert_indep : M₁.Indep (insert x (I ∩ U)) := by
      refine (M₁.indep_iff_eRk_eq_encard_of_finite (I := insert x (I ∩ U)) (by toFinite_tac)).2 ?_
      simpa [Set.encard_insert_of_notMem hx_not_mem_IU, hIU_indep.eRk_eq_encard] using hxrank
    have hx_ground : x ∈ M₁.E := hx_insert_indep.subset_ground (by simp)
    have hx_not_source : ¬ M₁.Indep (insert x I) := by
      intro hxsrc
      have hx_not_source_set : x ∉ SourceSet M₁ I :=
        (disjoint_right.mp hU.source_disjoint) hx_mem_U
      exact hx_not_source_set ⟨hx_not_mem_I, hxsrc⟩
    have hx_closure : x ∈ M₁.closure I := by
      by_contra hx_not_closure
      exact hx_not_source <|
        (hI.1.insert_indep_iff_of_notMem hx_not_mem_I).2 ⟨hx_ground, hx_not_closure⟩
    have hx_not_closure_IU : x ∉ M₁.closure (I ∩ U) := by
      have htmp := hx_insert_indep
      rw [hIU_indep.insert_indep_iff_of_notMem hx_not_mem_IU] at htmp
      exact htmp.2
    have hfund : M₁.IsCircuit (M₁.fundCircuit x I) :=
      hI.1.fundCircuit_isCircuit hx_closure hx_not_mem_I
    obtain ⟨y, hyDiff, hyNotU⟩ : ∃ y, y ∈ M₁.fundCircuit x I \ {x} ∧ y ∉ U := by
      by_contra hnone
      have hallU : M₁.fundCircuit x I \ {x} ⊆ I ∩ U := by
        intro y hy
        refine ⟨?_, ?_⟩
        · rw [M₁.fundCircuit_diff_eq_inter hx_not_mem_I] at hy
          exact hy.2
        · by_contra hyU
          exact hnone ⟨y, hy, hyU⟩
      exact hx_not_closure_IU <|
        M₁.closure_subset_closure hallU
          (hfund.mem_closure_diff_singleton_of_mem (M₁.mem_fundCircuit x I))
    have hyFund : y ∈ M₁.fundCircuit x I := hyDiff.1
    have hy_mem_I : y ∈ I := by
      rw [M₁.fundCircuit_diff_eq_inter hx_not_mem_I] at hyDiff
      exact hyDiff.2
    have hy_ne : y ≠ x := by simpa using hyDiff.2
    have hy_step' : M₁.Indep (insert x I \ {y}) :=
      (hI.1.mem_fundCircuit_iff hx_closure hx_not_mem_I).1 hyFund
    have hy_step : LeftArc M₁ I y x := by
      dsimp [LeftArc]
      simpa [insert_diff_singleton_comm hy_ne.symm, hx_not_mem_I] using hy_step'
    exact hyNotU (hU.left_closed hy_mem_I hx_not_mem_I hy_step hx_mem_U)
  · exact hIU_indep.encard_le_eRk_of_subset inter_subset_right

private theorem right_rank_eq_of_certificate [Finite α]
    (hE : SameGround M₁ M₂) (hI : CommonIndep M₁ M₂ I)
    (hU : TerminalCertificate M₁ M₂ I U) :
    M₂.eRk (M₁.E \ U) = (I \ U).encard := by
  have hI_diff_indep : M₂.Indep (I \ U) := hI.2.subset diff_subset
  apply le_antisymm
  · by_contra hlt
    have hlt' : M₂.eRk (I \ U) < M₂.eRk (M₁.E \ U) := by
      have hlt' : (I \ U).encard < M₂.eRk (M₁.E \ U) := lt_of_not_ge hlt
      rwa [← hI_diff_indep.eRk_eq_encard] at hlt'
    obtain ⟨x, hxEU, hxrank⟩ := M₂.exists_eRk_insert_eq_add_one_of_lt hlt'
    have hx_ground₁ : x ∈ M₁.E := hxEU.1.1
    have hx_not_mem_U : x ∉ U := hxEU.1.2
    have hx_not_mem_IU : x ∉ I \ U := hxEU.2
    have hx_not_mem_I : x ∉ I := by
      intro hxI
      exact hxEU.2 ⟨hxI, hx_not_mem_U⟩
    have hx_ground₂ : x ∈ M₂.E := by rwa [← hE]
    have hx_insert_indep : M₂.Indep (insert x (I \ U)) := by
      refine (M₂.indep_iff_eRk_eq_encard_of_finite (I := insert x (I \ U)) (by toFinite_tac)).2 ?_
      simpa [Set.encard_insert_of_notMem hx_not_mem_IU, hI_diff_indep.eRk_eq_encard] using hxrank
    have hx_not_sink : ¬ M₂.Indep (insert x I) := by
      intro hxsink
      exact hx_not_mem_U (hU.sinks_subset ⟨hx_not_mem_I, hxsink⟩)
    have hx_closure : x ∈ M₂.closure I := by
      by_contra hx_not_closure
      exact hx_not_sink <|
        (hI.2.insert_indep_iff_of_notMem hx_not_mem_I).2 ⟨hx_ground₂, hx_not_closure⟩
    have hx_not_closure_diff : x ∉ M₂.closure (I \ U) := by
      have htmp := hx_insert_indep
      rw [hI_diff_indep.insert_indep_iff_of_notMem hx_not_mem_IU] at htmp
      exact htmp.2
    have hfund : M₂.IsCircuit (M₂.fundCircuit x I) :=
      hI.2.fundCircuit_isCircuit hx_closure hx_not_mem_I
    obtain ⟨y, hyDiff, hyU⟩ : ∃ y, y ∈ M₂.fundCircuit x I \ {x} ∧ y ∈ U := by
      by_contra hnone
      have hallDiff : M₂.fundCircuit x I \ {x} ⊆ I \ U := by
        intro y hy
        refine ⟨?_, ?_⟩
        · rw [M₂.fundCircuit_diff_eq_inter hx_not_mem_I] at hy
          exact hy.2
        · by_contra hyU
          exact hnone ⟨y, hy, hyU⟩
      exact hx_not_closure_diff <|
        M₂.closure_subset_closure hallDiff
          (hfund.mem_closure_diff_singleton_of_mem (M₂.mem_fundCircuit x I))
    have hyFund : y ∈ M₂.fundCircuit x I := hyDiff.1
    have hy_mem_I : y ∈ I := by
      rw [M₂.fundCircuit_diff_eq_inter hx_not_mem_I] at hyDiff
      exact hyDiff.2
    have hy_ne : y ≠ x := by simpa using hyDiff.2
    have hy_step' : M₂.Indep (insert x I \ {y}) :=
      (hI.2.mem_fundCircuit_iff hx_closure hx_not_mem_I).1 hyFund
    have hy_step : LeftArc M₂ I y x := by
      dsimp [LeftArc]
      simpa [insert_diff_singleton_comm hy_ne.symm, hx_not_mem_I] using hy_step'
    exact hx_not_mem_U (hU.right_closed hx_not_mem_I hy_mem_I hy_step hyU)
  · have hsubset : I \ U ⊆ M₁.E \ U := by
      intro z hz
      exact ⟨hI.1.subset_ground hz.1, hz.2⟩
    exact hI_diff_indep.encard_le_eRk_of_subset hsubset

/-- The reachable-set certificate from Edmonds' algorithm proves maximality of the current
common independent set. -/
theorem optimal_of_certificate [Finite α]
    (hE : SameGround M₁ M₂) (hI : CommonIndep M₁ M₂ I)
    (hU : TerminalCertificate M₁ M₂ I U) :
    ∀ ⦃J⦄, CommonIndep M₁ M₂ J → J.encard ≤ I.encard := by
  intro J hJ
  have hleft := left_rank_eq_of_certificate hE hI hU
  have hright := right_rank_eq_of_certificate hE hI hU
  have hJ_left : M₁.Indep (J ∩ U) := hJ.1.subset inter_subset_left
  have hJ_right : M₂.Indep (J ∩ (M₁.E \ U)) := hJ.2.subset inter_subset_left
  have hJ_partition : J = (J ∩ U) ∪ (J ∩ (M₁.E \ U)) := by
    ext z
    constructor
    · intro hzJ
      by_cases hzU : z ∈ U
      · exact Or.inl ⟨hzJ, hzU⟩
      · exact Or.inr ⟨hzJ, hJ.1.subset_ground hzJ, hzU⟩
    · intro hz
      exact hz.elim (fun hzL ↦ hzL.1) (fun hzR ↦ hzR.1)
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
    _ = (I ∩ U).encard + M₂.eRk (M₁.E \ U) := by rw [hleft]
    _ = (I ∩ U).encard + (I \ U).encard := by rw [hright]
    _ = I.encard := by
      simpa [add_comm] using Set.encard_diff_add_encard_of_subset
        (s := I ∩ U) (t := I) inter_subset_left

/-- For a terminal-certified common independent set, the cardinality equals the rank-partition
value `M₁.eRk U + M₂.eRk (M₁.E \ U)` at the certificate set `U`. -/
theorem TerminalCertificate.encard_eq_rank_partition [Finite α]
    (hE : SameGround M₁ M₂) (hI : CommonIndep M₁ M₂ I)
    (hU : TerminalCertificate M₁ M₂ I U) :
    I.encard = M₁.eRk U + M₂.eRk (M₁.E \ U) := by
  rw [left_rank_eq_of_certificate hE hI hU, right_rank_eq_of_certificate hE hI hU]
  simpa [add_comm] using
    (Set.encard_diff_add_encard_of_subset (s := I ∩ U) (t := I) inter_subset_left).symm

/-- If no source can reach a sink in the exchange graph, the reachable set is a terminal
certificate. -/
theorem reachable_certificate
    (hNo : Disjoint (SourceSet M₁ I) (ReachableToSink M₁ M₂ I)) :
    TerminalCertificate M₁ M₂ I (ReachableToSink M₁ M₂ I) := by
  refine ⟨?_, ?_, ?_, hNo⟩
  · intro x hx
    exact ⟨x, hx, Relation.ReflTransGen.refl⟩
  · intro y x hyI hxI hleft hxReach
    rcases hxReach with ⟨z, hzSink, hxz⟩
    exact ⟨z, hzSink,
      Relation.ReflTransGen.head
        (Or.inl ⟨hyI, by exact fun h => hxI (h ▸ hyI), hxI, hleft⟩) hxz⟩
  · intro x y hxI hyI hright hyReach
    rcases hyReach with ⟨z, hzSink, hyz⟩
    exact ⟨z, hzSink,
      Relation.ReflTransGen.head
        (Or.inr ⟨hxI, by exact fun h => hxI (h ▸ hyI), hyI, hright⟩) hyz⟩

/-- Edmonds' terminal criterion: if no source reaches a sink in the exchange graph, then the
current common independent set is maximum. -/
theorem optimal_of_noAugmentingPath [Finite α]
    (hE : SameGround M₁ M₂) (hI : CommonIndep M₁ M₂ I)
    (hNo : Terminal M₁ M₂ I) :
    ∀ ⦃J⦄, CommonIndep M₁ M₂ J → J.encard ≤ I.encard :=
  optimal_of_certificate hE hI (reachable_certificate hNo)

/-- End-to-end abstract correctness: any run that repeatedly augments along certified
no-shortcut paths and stops at Edmonds' terminal condition ends in an optimal common
independent set. -/
theorem run_correct [Finite α] {I₀ I : Set α}
    (hE : SameGround M₁ M₂) (h₀ : CommonIndep M₁ M₂ I₀)
    (hRun : Run M₁ M₂ I₀ I) (hTerm : Terminal M₁ M₂ I) :
    ∀ ⦃J⦄, CommonIndep M₁ M₂ J → J.encard ≤ I.encard := by
  exact optimal_of_noAugmentingPath hE (commonIndep_of_run h₀ hRun) hTerm

/-- Any certified augmentation run that has no outgoing augmentation step ends at an optimal
common independent set. -/
theorem run_correct_of_maximal [Finite α] {I₀ I : Set α}
    (hE : SameGround M₁ M₂) (h₀ : CommonIndep M₁ M₂ I₀)
    (hRun : Run M₁ M₂ I₀ I) (hNo : ¬ ∃ J, AugmentStep M₁ M₂ I J) :
    ∀ ⦃J⦄, CommonIndep M₁ M₂ J → J.encard ≤ I.encard := by
  exact run_correct hE h₀ hRun (terminal_of_no_augmentStep hNo)

/-- Starting from any state, some certified augmentation run reaches a terminal exchange-graph
condition. -/
theorem exists_terminal_run [Finite α] {I : Set α} :
    ∃ J, Run M₁ M₂ I J ∧ Terminal M₁ M₂ J := by
  let C : Set α → Prop := fun S => ∃ J, Run M₁ M₂ S J ∧ Terminal M₁ M₂ J
  change C I
  have hacc : Acc (flip (AugmentStep M₁ M₂)) I := augmentStep_wf.apply I
  refine Acc.recOn hacc ?_
  intro S _ ih
  change C S
  by_cases hTerm : Terminal M₁ M₂ S
  · exact ⟨S, Relation.ReflTransGen.refl, hTerm⟩
  · rcases exists_augmentStep_of_nonterminal hTerm with ⟨T, hStep⟩
    rcases ih T hStep with ⟨J, hRun, hJterm⟩
    exact ⟨J, Relation.ReflTransGen.head hStep hRun, hJterm⟩

/-- Abstract Edmonds correctness: from any common independent set, some certified augmenting run
terminates at an optimal common independent set. -/
theorem exists_optimal_terminal_run [Finite α] {I : Set α}
    (hE : SameGround M₁ M₂) (hI : CommonIndep M₁ M₂ I) :
    ∃ J, Run M₁ M₂ I J ∧ Terminal M₁ M₂ J ∧
      ∀ ⦃K⦄, CommonIndep M₁ M₂ K → K.encard ≤ J.encard := by
  rcases exists_terminal_run (M₁ := M₁) (M₂ := M₂) (I := I) with ⟨J, hRun, hTerm⟩
  exact ⟨J, hRun, hTerm, run_correct hE hI hRun hTerm⟩

end TerminalOptimality

end Matroid.Intersection
