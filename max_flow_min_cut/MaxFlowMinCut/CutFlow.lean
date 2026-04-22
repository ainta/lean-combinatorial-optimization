import Mathlib.Algebra.Order.BigOperators.Group.Finset
import MaxFlowMinCut.Network

/-!
# Net flow across a cut, and the weak duality bound

This module proves the technical sum-decomposition lemmas relating the in/out-of-set sums
(`outAcross`, `inAcross`) to the per-vertex bookkeeping (`outflow`, `inflow`), culminating in
`netOn_eq_cutFlow` and `value_le_cutCapacity` — the weak-duality direction of max-flow / min-cut:
every flow value is bounded above by every cut capacity.
-/

open scoped BigOperators

namespace MaxFlowMinCut

section Network

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Flow

variable {N : Network (V := V)}

lemma outAcross_eq_filter_aux (f : Flow N) (S : Finset V) (u : V) :
    Finset.sum Finset.univ (fun v => if v ∈ S then 0 else f.val u v) =
      Finset.sum (Finset.univ.filter fun v => v ∉ S) (fun v => f.val u v) := by
  calc
    Finset.sum Finset.univ (fun v => if v ∈ S then 0 else f.val u v)
      = Finset.sum Finset.univ (fun v => if v ∉ S then f.val u v else 0) := by
          simp
    _ = Finset.sum (Finset.univ.filter fun v => v ∉ S) (fun v => f.val u v) := by
          symm
          exact Finset.sum_filter (p := fun v => v ∉ S) (f := fun v => f.val u v)

lemma inAcross_eq_filter_aux (f : Flow N) (S : Finset V) (u : V) :
    Finset.sum Finset.univ (fun v => if v ∈ S then 0 else f.val v u) =
      Finset.sum (Finset.univ.filter fun v => v ∉ S) (fun v => f.val v u) := by
  calc
    Finset.sum Finset.univ (fun v => if v ∈ S then 0 else f.val v u)
      = Finset.sum Finset.univ (fun v => if v ∉ S then f.val v u else 0) := by
          simp
    _ = Finset.sum (Finset.univ.filter fun v => v ∉ S) (fun v => f.val v u) := by
          symm
          exact Finset.sum_filter (p := fun v => v ∉ S) (f := fun v => f.val v u)

lemma outflow_split (f : Flow N) (S : Finset V) (u : V) :
    f.outflow u =
      Finset.sum S (fun v => f.val u v) +
        Finset.sum (Finset.univ.filter fun v => v ∉ S) (fun v => f.val u v) := by
  unfold outflow
  symm
  simpa [Finset.mem_filter] using
    (Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun v => v ∈ S)
      (f := fun v => f.val u v))

lemma inflow_split (f : Flow N) (S : Finset V) (u : V) :
    f.inflow u =
      Finset.sum S (fun v => f.val v u) +
        Finset.sum (Finset.univ.filter fun v => v ∉ S) (fun v => f.val v u) := by
  unfold inflow
  symm
  simpa [Finset.mem_filter] using
    (Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun v => v ∈ S)
      (f := fun v => f.val v u))

lemma outAcross_eq_filter (f : Flow N) (S : Finset V) :
    f.outAcross S =
      Finset.sum S
        (fun u => Finset.sum (Finset.univ.filter fun v => v ∉ S) (fun v => f.val u v)) := by
  unfold outAcross
  refine Finset.sum_congr rfl ?_
  intro u hu
  exact outAcross_eq_filter_aux f S u

lemma inAcross_eq_filter (f : Flow N) (S : Finset V) :
    f.inAcross S =
      Finset.sum S
        (fun u => Finset.sum (Finset.univ.filter fun v => v ∉ S) (fun v => f.val v u)) := by
  unfold inAcross
  refine Finset.sum_congr rfl ?_
  intro u hu
  exact inAcross_eq_filter_aux f S u

lemma outflow_sum_eq (f : Flow N) (S : Finset V) :
    Finset.sum S f.outflow =
      Finset.sum S (fun u => Finset.sum S (fun v => f.val u v)) + f.outAcross S := by
  rw [outAcross_eq_filter]
  calc
    Finset.sum S f.outflow =
        Finset.sum S (fun u =>
          Finset.sum S (fun v => f.val u v) +
            Finset.sum (Finset.univ.filter fun v => v ∉ S) (fun v => f.val u v)) := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              exact outflow_split f S u
    _ = Finset.sum S (fun u => Finset.sum S (fun v => f.val u v)) +
          Finset.sum S (fun u =>
            Finset.sum (Finset.univ.filter fun v => v ∉ S) (fun v => f.val u v)) := by
              rw [Finset.sum_add_distrib]

lemma inflow_sum_eq (f : Flow N) (S : Finset V) :
    Finset.sum S f.inflow =
      Finset.sum S (fun u => Finset.sum S (fun v => f.val v u)) + f.inAcross S := by
  rw [inAcross_eq_filter]
  calc
    Finset.sum S f.inflow =
        Finset.sum S (fun u =>
          Finset.sum S (fun v => f.val v u) +
            Finset.sum (Finset.univ.filter fun v => v ∉ S) (fun v => f.val v u)) := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              exact inflow_split f S u
    _ = Finset.sum S (fun u => Finset.sum S (fun v => f.val v u)) +
          Finset.sum S (fun u =>
            Finset.sum (Finset.univ.filter fun v => v ∉ S) (fun v => f.val v u)) := by
              rw [Finset.sum_add_distrib]

lemma internal_sum_comm (f : Flow N) (S : Finset V) :
    Finset.sum S (fun u => Finset.sum S (fun v => f.val v u)) =
      Finset.sum S (fun u => Finset.sum S (fun v => f.val u v)) := by
  rw [Finset.sum_comm]

lemma netOn_eq_cutFlow (f : Flow N) (S : Finset V) :
    f.netOn S = f.cutFlow S := by
  unfold netOn cutFlow
  change (Finset.sum S fun v => (f.outflow v : ℤ)) - Finset.sum S (fun v => (f.inflow v : ℤ)) =
    ↑(f.outAcross S) - ↑(f.inAcross S)
  have hout : (↑(Finset.sum S f.outflow) : ℤ) =
      ↑(Finset.sum S (fun u => Finset.sum S (fun v => f.val u v)) + f.outAcross S) := by
    exact congrArg (fun n : ℕ => (n : ℤ)) (outflow_sum_eq f S)
  have hin : (↑(Finset.sum S f.inflow) : ℤ) =
      ↑(Finset.sum S (fun u => Finset.sum S (fun v => f.val v u)) + f.inAcross S) := by
    exact congrArg (fun n : ℕ => (n : ℤ)) (inflow_sum_eq f S)
  have hcomm : (↑(Finset.sum S (fun u => Finset.sum S (fun v => f.val v u))) : ℤ) =
      ↑(Finset.sum S (fun u => Finset.sum S (fun v => f.val u v))) := by
    exact congrArg (fun n : ℕ => (n : ℤ)) (internal_sum_comm f S)
  simp only [Nat.cast_add] at hout hin hcomm
  calc
    Finset.sum S (fun v => (f.outflow v : ℤ)) - Finset.sum S (fun v => (f.inflow v : ℤ))
      = (↑(Finset.sum S f.outflow) : ℤ) - ↑(Finset.sum S f.inflow) := by
          simp
    _
      = (↑(Finset.sum S (fun u => Finset.sum S (fun v => f.val u v))) + ↑(f.outAcross S)) -
          (↑(Finset.sum S (fun u => Finset.sum S (fun v => f.val v u))) + ↑(f.inAcross S)) := by
            rw [hout, hin]
    _ = ↑(f.outAcross S) - ↑(f.inAcross S) := by
          rw [hcomm]
          ring

lemma outAcross_le_cutCapacity (f : Flow N) (S : Finset V) :
    f.outAcross S ≤ cutCapacity N S := by
  unfold outAcross cutCapacity
  refine Finset.sum_le_sum ?_
  intro u hu
  refine Finset.sum_le_sum ?_
  intro v hv
  by_cases hvS : v ∈ S
  · simp [hvS]
  · simp [hvS, f.le_cap u v]

lemma value_le_cutCapacity (f : Flow N) {S : Finset V} (hS : IsCut N S) :
    f.value ≤ cutCapacity N S := by
  have hvalue : (f.value : ℤ) = ↑(f.outAcross S) - ↑(f.inAcross S) := by
    calc
      (f.value : ℤ) = f.netOn S := by
        symm
        exact netOn_eq_value_of_isCut f hS
      _ = f.cutFlow S := netOn_eq_cutFlow f S
  have hcap : (f.outAcross S : ℤ) ≤ cutCapacity N S := by
    exact_mod_cast outAcross_le_cutCapacity f S
  omega

end Flow

end Network

end MaxFlowMinCut
