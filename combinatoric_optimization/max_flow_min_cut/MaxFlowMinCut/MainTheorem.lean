import MaxFlowMinCut.Augment

/-!
# The max-flow / min-cut theorem

Putting the augmentation step together with the cut bound: every network admits a flow with no
residual `source → sink` path (`exists_terminalFlow`), and any such flow is simultaneously a
maximum flow and witnesses a minimum cut whose capacity equals the flow value.
-/

namespace MaxFlowMinCut

section Network

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Flow

variable {N : Network (V := V)}

lemma source_singleton_isCut : IsCut N ({N.source} : Finset V) := by
  refine ⟨by simp, ?_⟩
  simpa [Finset.mem_singleton] using N.source_ne_sink.symm

theorem exists_terminalFlow_from (f : Flow N) :
    ∃ g : Flow N, f.value ≤ g.value ∧ ¬ Nonempty (ResidualPath g N.source N.sink) := by
  let C := cutCapacity N ({N.source} : Finset V)
  have hmain :
      ∀ n : ℕ, ∀ f : Flow N, C - f.value = n →
        ∃ g : Flow N, f.value ≤ g.value ∧ ¬ Nonempty (ResidualPath g N.source N.sink) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro f hgap
        by_cases hNo : Nonempty (ResidualPath f N.source N.sink)
        · rcases hNo with ⟨p⟩
          obtain ⟨g, hfg⟩ := exists_better_flow_of_residualPath p
          have hboundg : g.value ≤ C := by
            simpa [C] using value_le_cutCapacity g source_singleton_isCut
          have hlt : C - g.value < n := by
            have : C - g.value < C - f.value := by
              omega
            simpa [hgap] using this
          obtain ⟨hflow, hge, hterm⟩ := ih (C - g.value) hlt g rfl
          exact ⟨hflow, le_trans (Nat.le_of_lt hfg) hge, hterm⟩
        · exact ⟨f, le_rfl, hNo⟩
  exact hmain (C - f.value) f rfl

def zeroFlow : Flow N where
  val := fun _ _ => 0
  le_cap := by intro u v; simp
  conserve := by intro v hvs hvt; simp

theorem exists_terminalFlow :
    ∃ f : Flow N, ¬ Nonempty (ResidualPath f N.source N.sink) := by
  obtain ⟨f, hge, hNo⟩ := exists_terminalFlow_from (N := N) (zeroFlow (N := N))
  exact ⟨f, hNo⟩

theorem exists_isMaxFlow_and_isMinCut :
    ∃ f : Flow N, ∃ S : Finset V, IsMaxFlow f ∧ IsMinCut (N := N) S := by
  obtain ⟨f, hNo⟩ := exists_terminalFlow (N := N)
  exact ⟨f, f.reachable, isMaxFlow_and_isMinCut_of_noResidualPath hNo⟩

theorem exists_isMaxFlow_and_isMinCut_and_value_eq_cutCapacity :
    ∃ f : Flow N, ∃ S : Finset V,
      IsMaxFlow f ∧ IsMinCut (N := N) S ∧ f.value = cutCapacity N S := by
  obtain ⟨f, hNo⟩ := exists_terminalFlow (N := N)
  refine ⟨f, f.reachable, ?_⟩
  exact ⟨
    (isMaxFlow_and_isMinCut_of_noResidualPath hNo).1,
    (isMaxFlow_and_isMinCut_of_noResidualPath hNo).2,
    value_eq_cutCapacity_reachable hNo
  ⟩

theorem exists_maxFlow_value_eq_minCut_capacity :
    ∃ n : ℕ,
      (∃ f : Flow N, IsMaxFlow f ∧ f.value = n) ∧
      ∃ S : Finset V, IsMinCut (N := N) S ∧ cutCapacity N S = n := by
  obtain ⟨f, S, hmax, hmin, heq⟩ := exists_isMaxFlow_and_isMinCut_and_value_eq_cutCapacity (N := N)
  refine ⟨f.value, ?_⟩
  refine ⟨⟨f, hmax, rfl⟩, ?_⟩
  exact ⟨S, hmin, by simpa [heq]⟩

end Flow

end Network

end MaxFlowMinCut
