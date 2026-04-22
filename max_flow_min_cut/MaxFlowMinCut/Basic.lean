import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Data.List.Duplicate
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace MaxFlowMinCut

open Quiver Path

namespace Quiver.Path

open List

variable {V : Type*} [Quiver V] [DecidableEq V]

lemma length_cast {a b c : V} (h : a = b) (p : Path a c) : (h ▸ p).length = p.length := by
  cases h
  rfl

lemma end_eq {a b : V} (p : Quiver.Path a b) : p.end = b := by
  cases p <;> rfl

lemma shorten_of_not_nodup {a b : V} (p : Path a b) (hp : ¬ p.vertices.Nodup) :
    ∃ q : Path a b, q.length < p.length := by
  classical
  obtain ⟨v, hvdup⟩ := (List.exists_duplicate_iff_not_nodup).2 hp
  obtain ⟨n, m, hnm, hvn, hvm⟩ := (List.duplicate_iff_exists_distinct_get).1 hvdup
  obtain ⟨v₁, p₁, rest, hp_split_n, hp₁_len, hv₁⟩ :=
    p.exists_eq_comp_and_length_eq_of_lt_length n.val n.isLt
  obtain ⟨v₂, p₂, p₃, hp_split_m, hp₂_len, hv₂⟩ :=
    p.exists_eq_comp_and_length_eq_of_lt_length m.val m.isLt
  subst v₁
  subst v₂
  have hnm_le : n.val ≤ p₂.length := by simpa [hp₂_len] using Nat.le_of_lt hnm
  obtain ⟨w, p₁', cyc, hp₂_split, hp₁'_len⟩ := p₂.exists_eq_comp_of_le_length hnm_le
  have hp_as : p = p₁'.comp (cyc.comp p₃) := by
    calc
      p = p₂.comp p₃ := hp_split_m
      _ = (p₁'.comp cyc).comp p₃ := by rw [hp₂_split]
      _ = p₁'.comp (cyc.comp p₃) := by rw [comp_assoc]
  have hw : w = p.vertices.get n := by
    simpa [hp_as, hp₁'_len] using (vertices_comp_get_length_eq p₁' (cyc.comp p₃)).symm
  subst w
  have hvv : p.vertices[↑m] = p.vertices[↑n] := by simpa using (hvm.symm.trans hvn)
  have hsame : p₁.comp rest = p₁'.comp (cyc.comp p₃) := by
    calc
      p₁.comp rest = p := hp_split_n.symm
      _ = p₁'.comp (cyc.comp p₃) := hp_as
  have hlen : p₁.length = p₁'.length := by simpa [hp₁_len, hp₁'_len]
  have hcomp := (Path.comp_inj' (p₁ := p₁) (p₂ := p₁') (q₁ := rest) (q₂ := cyc.comp p₃) hlen).1 hsame
  have hprefix : p₁ = p₁' := hcomp.1
  have hrest : rest = cyc.comp p₃ := hcomp.2
  subst hprefix
  have hcyc_pos : 0 < cyc.length := by
    have : m.val = n.val + cyc.length := by
      simpa [hp₁'_len, hp₂_len, Path.length_comp] using congrArg Path.length hp₂_split
    have hneq : cyc.length ≠ 0 := by
      intro hzero
      have : m.val = n.val := by simpa [hzero] using this
      exact (Nat.ne_of_lt hnm) this.symm
    exact Nat.pos_iff_ne_zero.mpr hneq
  let qtail : Path p.vertices[↑n] b := hvv ▸ p₃
  let q : Path a b := p₁.comp qtail
  refine ⟨q, ?_⟩
  have htail : qtail.length < cyc.length + p₃.length := by
    have hqtaillen : qtail.length = p₃.length := by simpa [qtail] using length_cast hvv p₃
    omega
  have : p₁.length + qtail.length < p₁.length + (cyc.length + p₃.length) := by
    exact Nat.add_lt_add_left htail _
  simpa [q, qtail, hp_split_n, hrest, Path.length_comp, Nat.add_assoc] using this

theorem exists_nodup_vertices {a b : V} (p : Path a b) : ∃ q : Path a b, q.vertices.Nodup := by
  classical
  have hP : ∀ n, ∀ {a b : V} (p : Path a b), p.length ≤ n → ∃ q : Path a b, q.vertices.Nodup := by
    intro n
    induction n with
    | zero =>
        intro a b p hp
        have hp0 : p.length = 0 := Nat.eq_zero_of_le_zero hp
        cases p with
        | nil => exact ⟨Path.nil, by simp⟩
        | cons p e => simp at hp0
    | succ n ih =>
        intro a b p hp
        by_cases hpNodup : p.vertices.Nodup
        · exact ⟨p, hpNodup⟩
        · obtain ⟨q, hq⟩ := shorten_of_not_nodup p hpNodup
          have hqle : q.length ≤ n := Nat.lt_succ_iff.mp (lt_of_lt_of_le hq hp)
          exact ih q hqle
  exact hP p.length p le_rfl

end Quiver.Path

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
      Finset.sum S (fun u => Finset.sum (Finset.univ.filter fun v => v ∉ S) (fun v => f.val u v)) := by
  unfold outAcross
  refine Finset.sum_congr rfl ?_
  intro u hu
  exact outAcross_eq_filter_aux f S u

lemma inAcross_eq_filter (f : Flow N) (S : Finset V) :
    f.inAcross S =
      Finset.sum S (fun u => Finset.sum (Finset.univ.filter fun v => v ∉ S) (fun v => f.val v u)) := by
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
          Finset.sum S (fun u => Finset.sum (Finset.univ.filter fun v => v ∉ S) (fun v => f.val u v)) := by
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
          Finset.sum S (fun u => Finset.sum (Finset.univ.filter fun v => v ∉ S) (fun v => f.val v u)) := by
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

def augOut (g : V → V → ℕ) (x : V) : ℕ :=
  Finset.sum Finset.univ (fun y => g x y)

def augIn (g : V → V → ℕ) (x : V) : ℕ :=
  Finset.sum Finset.univ (fun y => g y x)

def augBal (g : V → V → ℕ) (x : V) : ℤ :=
  (augOut g x : ℤ) - augIn g x

def addEntry (g : V → V → ℕ) (a b : V) : V → V → ℕ :=
  fun x y => if x = a ∧ y = b then g x y + 1 else g x y

def subEntry (g : V → V → ℕ) (a b : V) : V → V → ℕ :=
  fun x y => if x = a ∧ y = b then g x y - 1 else g x y

lemma augOut_addEntry (g : V → V → ℕ) (a b x : V) :
    augOut (addEntry g a b) x = augOut g x + if x = a then 1 else 0 := by
  by_cases hx : x = a
  · subst a
    unfold augOut addEntry
    calc
      Finset.sum Finset.univ (fun y => if x = x ∧ y = b then g x y + 1 else g x y)
        = Finset.sum Finset.univ (fun y => g x y + if b = y then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            by_cases hyb : b = y <;> simp [hyb, eq_comm]
      _ = Finset.sum Finset.univ (fun y => g x y) +
            Finset.sum Finset.univ (fun y => if b = y then 1 else 0) := by
              rw [Finset.sum_add_distrib]
      _ = Finset.sum Finset.univ (fun y => g x y) + 1 := by
            rw [Finset.sum_ite_eq]
            simp
      _ = augOut g x + if x = x then 1 else 0 := by simp [augOut]
  · unfold augOut addEntry
    simp [hx]

lemma augIn_addEntry (g : V → V → ℕ) (a b x : V) :
    augIn (addEntry g a b) x = augIn g x + if x = b then 1 else 0 := by
  by_cases hx : x = b
  · subst b
    unfold augIn addEntry
    calc
      Finset.sum Finset.univ (fun y => if y = a ∧ x = x then g y x + 1 else g y x)
        = Finset.sum Finset.univ (fun y => g y x + if a = y then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            by_cases hya : a = y <;> simp [hya, eq_comm]
      _ = Finset.sum Finset.univ (fun y => g y x) +
            Finset.sum Finset.univ (fun y => if a = y then 1 else 0) := by
              rw [Finset.sum_add_distrib]
      _ = Finset.sum Finset.univ (fun y => g y x) + 1 := by
            rw [Finset.sum_ite_eq]
            simp
      _ = augIn g x + if x = x then 1 else 0 := by simp [augIn]
  · unfold augIn addEntry
    simp [hx]

lemma augBal_addEntry (g : V → V → ℕ) (a b x : V) :
    augBal (addEntry g a b) x =
      augBal g x + (if x = a then 1 else 0) - (if x = b then 1 else 0) := by
  unfold augBal
  rw [augOut_addEntry, augIn_addEntry]
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp [hxa, hxb] <;> ring

lemma sum_subEntry_row (g : V → V → ℕ) (a b : V) (hpos : 0 < g a b) :
    (∑ y, (if y = b then g a y - 1 else g a y)) = (∑ y, g a y) - 1 := by
  rw [show (Finset.univ : Finset V) = insert b (Finset.univ.erase b) by simp]
  rw [Finset.sum_insert (Finset.notMem_erase _ _)]
  rw [Finset.sum_insert (Finset.notMem_erase _ _)]
  have hrest :
      Finset.sum (Finset.univ.erase b) (fun x => if x = b then g a x - 1 else g a x) =
        Finset.sum (Finset.univ.erase b) (fun x => g a x) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxb : x ≠ b := (Finset.mem_erase.mp hx).1
    simp [hxb]
  rw [hrest]
  simp
  omega

lemma sum_subEntry_col (g : V → V → ℕ) (a b : V) (hpos : 0 < g a b) :
    (∑ y, (if y = a then g y b - 1 else g y b)) = (∑ y, g y b) - 1 := by
  rw [show (Finset.univ : Finset V) = insert a (Finset.univ.erase a) by simp]
  rw [Finset.sum_insert (Finset.notMem_erase _ _)]
  rw [Finset.sum_insert (Finset.notMem_erase _ _)]
  have hrest :
      Finset.sum (Finset.univ.erase a) (fun x => if x = a then g x b - 1 else g x b) =
        Finset.sum (Finset.univ.erase a) (fun x => g x b) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxa : x ≠ a := (Finset.mem_erase.mp hx).1
    simp [hxa]
  rw [hrest]
  simp
  omega

lemma augOut_subEntry (g : V → V → ℕ) (a b x : V) (hab : 0 < g a b) :
    augOut (subEntry g a b) x = augOut g x - if x = a then 1 else 0 := by
  by_cases hx : x = a
  · subst x
    simpa [augOut, subEntry] using sum_subEntry_row g a b hab
  · unfold augOut subEntry
    simp [hx]

lemma augIn_subEntry (g : V → V → ℕ) (a b x : V) (hab : 0 < g a b) :
    augIn (subEntry g a b) x = augIn g x - if x = b then 1 else 0 := by
  by_cases hx : x = b
  · subst x
    simpa [augIn, subEntry] using sum_subEntry_col g a b hab
  · unfold augIn subEntry
    simp [hx]

lemma augBal_subEntry_of_ne (g : V → V → ℕ) (a b x : V) (hab : 0 < g a b) (hne : a ≠ b) :
    augBal (subEntry g a b) x =
      augBal g x - (if x = a then 1 else 0) + (if x = b then 1 else 0) := by
  unfold augBal
  rw [augOut_subEntry _ _ _ _ hab, augIn_subEntry _ _ _ _ hab]
  by_cases hxa : x = a
  · subst x
    have houtge : 1 ≤ augOut g a := by
      unfold augOut
      have hsingle : g a b ≤ ∑ y, g a y := by
        exact Finset.single_le_sum (fun y _ => Nat.zero_le (g a y)) (Finset.mem_univ b)
      exact le_trans hab hsingle
    rw [if_pos rfl, if_pos rfl, if_neg hne]
    rw [show ((augOut g a - 1 : ℕ) : ℤ) = (augOut g a : ℤ) - 1 by exact Int.ofNat_sub houtge]
    simp [hne]
    ring_nf
  · by_cases hxb : x = b
    · subst x
      have hInge : 1 ≤ augIn g b := by
        unfold augIn
        have hsingle : g a b ≤ ∑ y, g y b := by
          exact Finset.single_le_sum (fun y _ => Nat.zero_le (g y b)) (Finset.mem_univ a)
        exact le_trans hab hsingle
      have hne' : b ≠ a := by
        intro h
        exact hne h.symm
      rw [if_neg hne', if_pos rfl, if_pos rfl]
      rw [show ((augIn g b - 1 : ℕ) : ℤ) = (augIn g b : ℤ) - 1 by exact Int.ofNat_sub hInge]
      simp [hne']
      ring_nf
    · rw [if_neg hxa, if_neg hxb, if_neg hxa, if_neg hxb]
      simp

def augmentVal {f : Flow N} : {u v : V} → ResidualPath f u v → V → V → ℕ
  | _, _, p =>
      letI := residualQuiver f
      match p with
      | Quiver.Path.nil => f.val
      | Quiver.Path.cons p e =>
          match e with
          | ResidualEdge.forward _ => addEntry (augmentVal p) p.end (Quiver.Path.end (p.cons e))
          | ResidualEdge.backward _ => subEntry (augmentVal p) (Quiver.Path.end (p.cons e)) p.end

lemma augmentVal_eq_of_or_not_mem_vertices {f : Flow N} :
    ∀ {u v : V} (p : ResidualPath f u v) {x y : V},
      x ∉ (@Quiver.Path.vertices V (residualQuiver f) u v p) ∨
      y ∉ (@Quiver.Path.vertices V (residualQuiver f) u v p) →
      augmentVal p x y = f.val x y := by
  letI := residualQuiver f
  intro u v p
  induction p with
  | nil =>
      intro x y hxy
      simp [augmentVal]
  | cons p e ih =>
      intro x y hxy
      have hprev : x ∉ p.vertices ∨ y ∉ p.vertices := by
        cases hxy with
        | inl hx =>
            left
            intro hmem
            exact hx ((Quiver.Path.mem_vertices_cons p e).2 (Or.inl hmem))
        | inr hy =>
            right
            intro hmem
            exact hy ((Quiver.Path.mem_vertices_cons p e).2 (Or.inl hmem))
      have ih' := ih (x := x) (y := y) hprev
      cases e with
      | forward h =>
          have hne : ¬ (x = p.end ∧ y = (p.cons (ResidualEdge.forward h)).end) := by
            intro hxy'
            cases hxy with
            | inl hx =>
                exact hx ((Quiver.Path.mem_vertices_cons p (ResidualEdge.forward h)).2
                  (Or.inl (hxy'.1 ▸ Quiver.Path.end_mem_vertices p)))
            | inr hy =>
                exact hy ((Quiver.Path.mem_vertices_cons p (ResidualEdge.forward h)).2 (Or.inr hxy'.2))
          simp [augmentVal, addEntry]
          rw [if_neg (by simpa using hne), ih']
      | backward h =>
          have hne : ¬ (x = (p.cons (ResidualEdge.backward h)).end ∧ y = p.end) := by
            intro hxy'
            cases hxy with
            | inl hx =>
                exact hx ((Quiver.Path.mem_vertices_cons p (ResidualEdge.backward h)).2 (Or.inr hxy'.1))
            | inr hy =>
                exact hy ((Quiver.Path.mem_vertices_cons p (ResidualEdge.backward h)).2
                  (Or.inl (hxy'.2 ▸ Quiver.Path.end_mem_vertices p)))
          simp [augmentVal, subEntry]
          rw [if_neg (by simpa using hne), ih']

lemma augmentVal_le_cap_of_nodup {f : Flow N} :
    ∀ {u v : V} (p : ResidualPath f u v),
      List.Nodup (@Quiver.Path.vertices V (residualQuiver f) u v p) →
      ∀ a b, augmentVal p a b ≤ N.cap a b := by
  letI := residualQuiver f
  intro u v p
  induction p with
  | nil =>
      intro hnodup a b
      simpa [augmentVal] using f.le_cap a b
  | cons p e ih =>
      intro hnodup a b
      rw [Quiver.Path.vertices_cons] at hnodup
      rcases (List.nodup_concat _ _).1 hnodup with ⟨hfresh, hnodup'⟩
      cases e with
      | forward h =>
          by_cases hab : a = p.end ∧ b = (p.cons (ResidualEdge.forward h)).end
          · rcases hab with ⟨rfl, rfl⟩
            have hunchanged :
                augmentVal p p.end (p.cons (ResidualEdge.forward h)).end =
                  f.val p.end (p.cons (ResidualEdge.forward h)).end := by
              apply augmentVal_eq_of_or_not_mem_vertices p
              exact Or.inr hfresh
            calc
              augmentVal (p.cons (ResidualEdge.forward h)) p.end
                  (p.cons (ResidualEdge.forward h)).end
                = augmentVal p p.end (p.cons (ResidualEdge.forward h)).end + 1 := by
                    simp [augmentVal, addEntry]
              _ = f.val p.end (p.cons (ResidualEdge.forward h)).end + 1 := by rw [hunchanged]
              _ ≤ N.cap p.end (p.cons (ResidualEdge.forward h)).end := Nat.succ_le_of_lt h
          · calc
              augmentVal (p.cons (ResidualEdge.forward h)) a b = augmentVal p a b := by
                rw [augmentVal, addEntry, if_neg hab]
              _ ≤ N.cap a b := ih hnodup' a b
      | backward h =>
          by_cases hab : a = (p.cons (ResidualEdge.backward h)).end ∧ b = p.end
          · rcases hab with ⟨rfl, rfl⟩
            have hunchanged :
                augmentVal p (p.cons (ResidualEdge.backward h)).end p.end =
                  f.val (p.cons (ResidualEdge.backward h)).end p.end := by
              apply augmentVal_eq_of_or_not_mem_vertices p
              exact Or.inl hfresh
            have hle :
                augmentVal p (p.cons (ResidualEdge.backward h)).end p.end - 1 ≤
                  N.cap (p.cons (ResidualEdge.backward h)).end p.end := by
              rw [hunchanged]
              exact le_trans (Nat.sub_le _ _) (f.le_cap _ _)
            calc
              augmentVal (p.cons (ResidualEdge.backward h))
                  (p.cons (ResidualEdge.backward h)).end p.end
                = augmentVal p (p.cons (ResidualEdge.backward h)).end p.end - 1 := by
                    simp [augmentVal, subEntry]
              _ ≤ N.cap (p.cons (ResidualEdge.backward h)).end p.end := hle
          · calc
              augmentVal (p.cons (ResidualEdge.backward h)) a b = augmentVal p a b := by
                rw [augmentVal, subEntry, if_neg hab]
              _ ≤ N.cap a b := ih hnodup' a b

lemma augBal_augmentVal_of_nodup {f : Flow N} :
    ∀ {u v : V} (p : ResidualPath f u v),
      List.Nodup (@Quiver.Path.vertices V (residualQuiver f) u v p) →
      ∀ x,
        augBal (augmentVal p) x =
          augBal f.val x + (if x = u then 1 else 0) - (if x = v then 1 else 0) := by
  letI := residualQuiver f
  intro u v p
  induction p with
  | nil =>
      intro hnodup x
      by_cases hx : x = u
      · subst x
        simp [augmentVal, augBal]
      · simp [augmentVal, augBal, hx]
  | cons p e ih =>
      intro hnodup x
      rw [Quiver.Path.vertices_cons] at hnodup
      rcases (List.nodup_concat _ _).1 hnodup with ⟨hfresh, hnodup'⟩
      cases e with
      | forward h =>
          have hne : (p.cons (ResidualEdge.forward h)).end ≠ p.end := by
            intro hEq
            have hcb : (p.cons (ResidualEdge.forward h)).end = p.end := hEq
            have hcb' := hcb
            simp [Quiver.Path.end_eq p] at hcb'
            apply hfresh
            rw [hcb']
            exact Quiver.Path.end_mem_vertices p
          have hpenew : p.end ≠ (p.cons (ResidualEdge.forward h)).end := by
            intro hEq
            exact hne hEq.symm
          have ihx := ih hnodup' x
          calc
            augBal (augmentVal (p.cons (ResidualEdge.forward h))) x
              = augBal (augmentVal p) x +
                  (if x = p.end then 1 else 0) -
                  (if x = (p.cons (ResidualEdge.forward h)).end then 1 else 0) := by
                    simpa [augmentVal] using
                      (augBal_addEntry (g := augmentVal p) (a := p.end)
                        (b := (p.cons (ResidualEdge.forward h)).end) (x := x))
            _ = augBal f.val x + (if x = u then 1 else 0) -
                  (if x = (p.cons (ResidualEdge.forward h)).end then 1 else 0) := by
                    rw [ihx, Quiver.Path.end_eq p]
                    by_cases hxp : x = p.end
                    · have hxnew : x ≠ (p.cons (ResidualEdge.forward h)).end := by
                        intro hEq
                        exact hne (hEq.symm.trans hxp)
                      simp [hxp, hxnew, hpenew]
                    · simp [hxp, Quiver.Path.end_eq p]
      | backward h =>
          have hne : (p.cons (ResidualEdge.backward h)).end ≠ p.end := by
            intro hEq
            have hcb : (p.cons (ResidualEdge.backward h)).end = p.end := hEq
            have hcb' := hcb
            simp [Quiver.Path.end_eq p] at hcb'
            apply hfresh
            rw [hcb']
            exact Quiver.Path.end_mem_vertices p
          have hpenew : p.end ≠ (p.cons (ResidualEdge.backward h)).end := by
            intro hEq
            exact hne hEq.symm
          have ihx := ih hnodup' x
          have hunchanged :
              augmentVal p (p.cons (ResidualEdge.backward h)).end p.end =
                f.val (p.cons (ResidualEdge.backward h)).end p.end := by
            apply augmentVal_eq_of_or_not_mem_vertices p
            exact Or.inl hfresh
          have hpos : 0 < augmentVal p (p.cons (ResidualEdge.backward h)).end p.end := by
            rw [hunchanged]
            exact h
          calc
            augBal (augmentVal (p.cons (ResidualEdge.backward h))) x
              = augBal (augmentVal p) x -
                  (if x = (p.cons (ResidualEdge.backward h)).end then 1 else 0) +
                  (if x = p.end then 1 else 0) := by
                    simpa [augmentVal] using
                      (augBal_subEntry_of_ne (g := augmentVal p)
                        (a := (p.cons (ResidualEdge.backward h)).end)
                        (b := p.end) (x := x) hpos hne)
            _ = augBal f.val x + (if x = u then 1 else 0) -
                  (if x = (p.cons (ResidualEdge.backward h)).end then 1 else 0) := by
                    rw [ihx, Quiver.Path.end_eq p]
                    by_cases hxp : x = p.end
                    · have hxnew : x ≠ (p.cons (ResidualEdge.backward h)).end := by
                        intro hEq
                        exact hne (hEq.symm.trans hxp)
                      simp [hxp, hxnew, hpenew]
                      omega
                    · simp [hxp, Quiver.Path.end_eq p]
                      omega

theorem exists_simple_residualPath {f : Flow N} {u v : V} (p : ResidualPath f u v) :
    ∃ q : ResidualPath f u v, List.Nodup (@Quiver.Path.vertices V (residualQuiver f) u v q) := by
  letI := residualQuiver f
  simpa using Quiver.Path.exists_nodup_vertices p

lemma augBal_eq_zero_of_conserve (f : Flow N) {x : V}
    (hxsrc : x ≠ N.source) (hxsink : x ≠ N.sink) :
    augBal f.val x = 0 := by
  unfold augBal augOut augIn
  have hcons := f.conserve x hxsrc hxsink
  omega

lemma augBal_source_eq_value (f : Flow N) :
    augBal f.val N.source = f.value := by
  unfold augBal augOut augIn value outflow
  rw [show (∑ y, f.val y N.source) = f.inflow N.source by rfl]
  rw [inflow_source_eq_zero]
  simp

lemma exists_augmentedFlow_of_simple_residualPath {f : Flow N}
    (p : ResidualPath f N.source N.sink)
    (hp : List.Nodup (@Quiver.Path.vertices V (residualQuiver f) N.source N.sink p)) :
    ∃ g : Flow N, g.value = f.value + 1 := by
  let g : Flow N :=
    { val := augmentVal p
      le_cap := augmentVal_le_cap_of_nodup p hp
      conserve := by
        intro x hxsrc hxsink
        have hbal : augBal (augmentVal p) x = 0 := by
          rw [augBal_augmentVal_of_nodup p hp x]
          simp [hxsrc, hxsink, augBal_eq_zero_of_conserve f hxsrc hxsink]
        unfold augBal augOut augIn at hbal
        omega }
  refine ⟨g, ?_⟩
  have hsource : augBal (augmentVal p) N.source = augBal f.val N.source + 1 := by
    have := augBal_augmentVal_of_nodup p hp N.source
    simpa [N.source_ne_sink] using this
  have hgsource : augBal g.val N.source = g.value := by
    unfold g
    simpa using augBal_source_eq_value (f := g)
  have hInt : (g.value : ℤ) = f.value + 1 := by
    calc
      (g.value : ℤ) = augBal g.val N.source := by rw [hgsource]
      _ = augBal f.val N.source + 1 := hsource
      _ = f.value + 1 := by rw [augBal_source_eq_value]
  exact_mod_cast hInt

lemma exists_better_flow_of_residualPath {f : Flow N}
    (p : ResidualPath f N.source N.sink) :
    ∃ g : Flow N, f.value < g.value := by
  obtain ⟨q, hq⟩ := exists_simple_residualPath p
  obtain ⟨g, hg⟩ := exists_augmentedFlow_of_simple_residualPath q hq
  refine ⟨g, ?_⟩
  rw [hg]
  exact Nat.lt_succ_self _

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
