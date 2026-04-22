import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Data.List.Duplicate
import Mathlib.Tactic

/-!
# Path-shortening lemmas for `Quiver.Path`

Generic helpers used by the residual-graph construction: any path with a duplicate vertex can be
shortened by excising the cycle, so every reachable endpoint admits a path with `Nodup`
vertices. These lemmas only depend on the abstract `Quiver` API.
-/

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

end MaxFlowMinCut
