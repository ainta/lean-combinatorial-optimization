import MaxFlowMinCut.QuiverPath
import MaxFlowMinCut.CutFlow

/-!
# The residual graph and the source-side reachable set

For a flow `f` on a network `N`, the residual graph has a forward edge `u → v` whenever
`f.val u v < N.cap u v` and a backward edge `u → v` whenever `0 < f.val v u`. The set
`f.reachable` of vertices reachable from `N.source` along residual paths is then a cut whenever
the sink is unreachable, and weak duality forces the flow value to equal the cut capacity. From
this we derive the "no residual path ⇒ max flow" half of the theorem (and the matching min-cut
witness).
-/

open Quiver

namespace MaxFlowMinCut

section Network

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Flow

variable {N : Network (V := V)}

inductive ResidualEdge (f : Flow N) : V → V → Type
  | forward {u v : V} (h : f.val u v < N.cap u v) : ResidualEdge f u v
  | backward {u v : V} (h : 0 < f.val v u) : ResidualEdge f u v

instance residualQuiver (f : Flow N) : Quiver V where
  Hom u v := ResidualEdge f u v

abbrev ResidualPath (f : Flow N) (u v : V) := @Quiver.Path V (residualQuiver f) u v

noncomputable def reachable (f : Flow N) : Finset V := by
  classical
  exact Finset.univ.filter fun v => Nonempty (ResidualPath f N.source v)

lemma mem_reachable_iff (f : Flow N) {v : V} :
    v ∈ f.reachable ↔ Nonempty (ResidualPath f N.source v) := by
  classical
  simp [reachable]

lemma source_mem_reachable (f : Flow N) : N.source ∈ f.reachable := by
  letI := residualQuiver f
  exact (mem_reachable_iff f).2 ⟨Path.nil⟩

lemma mem_reachable_of_mem_reachable_of_edge {f : Flow N} {u v : V}
    (hu : u ∈ f.reachable) (e : ResidualEdge f u v) : v ∈ f.reachable := by
  letI := residualQuiver f
  rcases (mem_reachable_iff f).1 hu with ⟨p⟩
  exact (mem_reachable_iff f).2 ⟨p.cons e⟩

lemma no_edge_of_mem_reachable_of_not_mem_reachable {f : Flow N} {u v : V}
    (hu : u ∈ f.reachable) (hv : v ∉ f.reachable) : IsEmpty (ResidualEdge f u v) := by
  refine ⟨?_⟩
  intro e
  exact hv (mem_reachable_of_mem_reachable_of_edge hu e)

lemma val_eq_cap_of_mem_reachable_of_not_mem_reachable {f : Flow N} {u v : V}
    (hu : u ∈ f.reachable) (hv : v ∉ f.reachable) : f.val u v = N.cap u v := by
  by_contra hneq
  have hlt : f.val u v < N.cap u v := Nat.lt_of_le_of_ne (f.le_cap u v) hneq
  exact (no_edge_of_mem_reachable_of_not_mem_reachable hu hv).false (ResidualEdge.forward hlt)

lemma val_rev_eq_zero_of_mem_reachable_of_not_mem_reachable {f : Flow N} {u v : V}
    (hu : u ∈ f.reachable) (hv : v ∉ f.reachable) : f.val v u = 0 := by
  by_contra hneq
  have hpos : 0 < f.val v u := Nat.pos_iff_ne_zero.mpr hneq
  exact (no_edge_of_mem_reachable_of_not_mem_reachable hu hv).false (ResidualEdge.backward hpos)

lemma reachable_isCut {f : Flow N}
    (hNo : ¬ Nonempty (ResidualPath f N.source N.sink)) : IsCut N f.reachable := by
  refine ⟨source_mem_reachable f, ?_⟩
  intro hsink
  exact hNo ((mem_reachable_iff f).1 hsink)

lemma outAcross_reachable_eq_cutCapacity (f : Flow N) :
    f.outAcross f.reachable = cutCapacity N f.reachable := by
  unfold outAcross cutCapacity
  refine Finset.sum_congr rfl ?_
  intro u hu
  refine Finset.sum_congr rfl ?_
  intro v hv
  by_cases hvR : v ∈ f.reachable
  · simp [hvR]
  · simp [hvR, val_eq_cap_of_mem_reachable_of_not_mem_reachable hu hvR]

lemma inAcross_reachable_eq_zero (f : Flow N) :
    f.inAcross f.reachable = 0 := by
  unfold inAcross
  refine Finset.sum_eq_zero ?_
  intro u hu
  refine Finset.sum_eq_zero ?_
  intro v hv
  by_cases hvR : v ∈ f.reachable
  · simp [hvR]
  · simp [hvR, val_rev_eq_zero_of_mem_reachable_of_not_mem_reachable hu hvR]

lemma value_eq_cutCapacity_reachable {f : Flow N}
    (hNo : ¬ Nonempty (ResidualPath f N.source N.sink)) :
    f.value = cutCapacity N f.reachable := by
  have hcut : IsCut N f.reachable := reachable_isCut hNo
  have hvalue : (f.value : ℤ) = f.cutFlow f.reachable := by
    calc
      (f.value : ℤ) = f.netOn f.reachable := by
        symm
        exact netOn_eq_value_of_isCut f hcut
      _ = f.cutFlow f.reachable := netOn_eq_cutFlow f f.reachable
  unfold cutFlow at hvalue
  rw [inAcross_reachable_eq_zero] at hvalue
  simp at hvalue
  have hout : f.outAcross f.reachable = cutCapacity N f.reachable :=
    outAcross_reachable_eq_cutCapacity f
  rw [hout] at hvalue
  exact_mod_cast hvalue

lemma isMaxFlow_of_noResidualPath {f : Flow N}
    (hNo : ¬ Nonempty (ResidualPath f N.source N.sink)) : IsMaxFlow f := by
  intro g
  have hcut : IsCut N f.reachable := reachable_isCut hNo
  have hweak : g.value ≤ cutCapacity N f.reachable := value_le_cutCapacity g hcut
  simpa [value_eq_cutCapacity_reachable hNo] using hweak

lemma isMinCut_reachable_of_noResidualPath {f : Flow N}
    (hNo : ¬ Nonempty (ResidualPath f N.source N.sink)) : IsMinCut (N := N) f.reachable := by
  refine ⟨reachable_isCut hNo, ?_⟩
  intro T hT
  have hweak : f.value ≤ cutCapacity N T := value_le_cutCapacity f hT
  simpa [value_eq_cutCapacity_reachable hNo] using hweak

lemma isMaxFlow_and_isMinCut_of_noResidualPath {f : Flow N}
    (hNo : ¬ Nonempty (ResidualPath f N.source N.sink)) :
    IsMaxFlow f ∧ IsMinCut (N := N) f.reachable := by
  exact ⟨isMaxFlow_of_noResidualPath hNo, isMinCut_reachable_of_noResidualPath hNo⟩

end Flow

end Network

end MaxFlowMinCut
