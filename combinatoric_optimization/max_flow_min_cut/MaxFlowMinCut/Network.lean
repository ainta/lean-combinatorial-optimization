import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Networks, flows, cuts, and basic conservation lemmas

The data layer of the max-flow / min-cut development:
- `Network`: a finite graph with capacities and a designated source / sink, where the source has
  no incoming capacity and the sink no outgoing.
- `Flow`: an assignment of nonnegative integers bounded by capacity, satisfying conservation at
  every interior vertex.
- `IsCut`, `cutCapacity`, `IsMaxFlow`, `IsMinCut`: the standard cut and optimality predicates.
- `outflow`, `inflow`, `value`, `outAcross`, `inAcross`, `netOn`, `cutFlow`: the bookkeeping
  quantities used to relate flow value to net flow across an arbitrary cut.

The headline lemmas of this module are `netOn_eq_zero_of_conserved_subset` (conservation at all
internal vertices means the net flow over a set of internal vertices is zero) and
`netOn_eq_value_of_isCut` (the net flow across a source-side cut equals the flow value).
-/

open scoped BigOperators

namespace MaxFlowMinCut

section Network

variable {V : Type*} [Fintype V] [DecidableEq V]

structure Network where
  source : V
  sink : V
  source_ne_sink : source ≠ sink
  cap : V → V → ℕ
  no_into_source : ∀ v, cap v source = 0
  no_out_of_sink : ∀ v, cap sink v = 0

structure Flow (N : Network (V := V)) where
  val : V → V → ℕ
  le_cap : ∀ u v, val u v ≤ N.cap u v
  conserve : ∀ v, v ≠ N.source → v ≠ N.sink →
    (∑ u, val u v) = ∑ w, val v w

namespace Flow

variable {N : Network (V := V)}

def outflow (f : Flow N) (v : V) : ℕ :=
  ∑ w, f.val v w

def inflow (f : Flow N) (v : V) : ℕ :=
  ∑ u, f.val u v

def value (f : Flow N) : ℕ :=
  f.outflow N.source

def IsCut (N : Network (V := V)) (S : Finset V) : Prop :=
  N.source ∈ S ∧ N.sink ∉ S

def cutCapacity (N : Network (V := V)) (S : Finset V) : ℕ :=
  S.sum fun u => ∑ v, if v ∈ S then 0 else N.cap u v

def outAcross (f : Flow N) (S : Finset V) : ℕ :=
  S.sum fun u => ∑ v, if v ∈ S then 0 else f.val u v

def inAcross (f : Flow N) (S : Finset V) : ℕ :=
  S.sum fun u => ∑ v, if v ∈ S then 0 else f.val v u

def netOn (f : Flow N) (S : Finset V) : ℤ :=
  (S.sum fun v => (f.outflow v : ℤ)) - (S.sum fun v => (f.inflow v : ℤ))

def cutFlow (f : Flow N) (S : Finset V) : ℤ :=
  (f.outAcross S : ℤ) - f.inAcross S

def IsMaxFlow (f : Flow N) : Prop :=
  ∀ g : Flow N, g.value ≤ f.value

def IsMinCut (S : Finset V) : Prop :=
  IsCut N S ∧ ∀ T : Finset V, IsCut N T → cutCapacity N S ≤ cutCapacity N T

lemma val_to_source_eq_zero (f : Flow N) (u : V) : f.val u N.source = 0 := by
  have hle := f.le_cap u N.source
  rw [N.no_into_source] at hle
  exact Nat.eq_zero_of_le_zero hle

lemma val_from_sink_eq_zero (f : Flow N) (v : V) : f.val N.sink v = 0 := by
  have hle := f.le_cap N.sink v
  rw [N.no_out_of_sink] at hle
  exact Nat.eq_zero_of_le_zero hle

lemma inflow_source_eq_zero (f : Flow N) : f.inflow N.source = 0 := by
  unfold inflow
  refine Finset.sum_eq_zero ?_
  intro u hu
  exact val_to_source_eq_zero f u

lemma netOn_empty (f : Flow N) : f.netOn ∅ = 0 := by
  simp [netOn]

lemma netOn_insert {f : Flow N} {S : Finset V} {x : V} (hx : x ∉ S) :
    f.netOn (insert x S) = f.netOn S + ((f.outflow x : ℤ) - f.inflow x) := by
  simp [netOn, hx, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma netOn_eq_zero_of_conserved_subset (f : Flow N) :
    ∀ {S : Finset V},
      (∀ v ∈ S, v ≠ N.source ∧ v ≠ N.sink) →
      f.netOn S = 0 := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro hS
      simp [netOn]
  | @insert x S hx ih =>
      intro hS
      have hxs : x ≠ N.source ∧ x ≠ N.sink := hS x (by simp)
      have hrest : ∀ v ∈ S, v ≠ N.source ∧ v ≠ N.sink := by
        intro v hv
        exact hS v (by simp [hv])
      have hcons : (f.outflow x : ℤ) - f.inflow x = 0 := by
        have hc : f.inflow x = f.outflow x := by
          simpa [outflow, inflow] using (f.conserve x hxs.1 hxs.2)
        omega
      rw [netOn_insert hx, ih hrest, hcons]
      simp

lemma netOn_eq_value_of_isCut (f : Flow N) {S : Finset V} (hS : IsCut N S) :
    f.netOn S = f.value := by
  let T := S.erase N.source
  have hT : ∀ v ∈ T, v ≠ N.source ∧ v ≠ N.sink := by
    intro v hv
    have hvS : v ∈ S := by exact Finset.mem_of_mem_erase hv
    exact ⟨by exact Finset.ne_of_mem_erase hv, by
      intro hEq
      subst hEq
      exact hS.2 hvS⟩
  have hsrc : N.source ∉ T := by simp [T]
  have hsplit : insert N.source T = S := by
    simpa [T] using Finset.insert_erase hS.1
  rw [← hsplit, netOn_insert hsrc, netOn_eq_zero_of_conserved_subset f hT, zero_add, value,
    inflow_source_eq_zero]
  simp [outflow]

end Flow

end Network

end MaxFlowMinCut
