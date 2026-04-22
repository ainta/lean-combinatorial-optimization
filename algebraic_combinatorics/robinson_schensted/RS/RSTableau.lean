import RS.TableauInsert

/-!
# Concrete RS tableau invariants

This file packages the row-list invariants relevant to the Robinson-Schensted development and
proves the first preservation result needed for the insertion tableau: row strictness is preserved
under insertion when the inserted value is globally fresh.
-/

namespace RS

/-- Every row in the list is strictly increasing. -/
def RowsStrict (rows : List Row) : Prop :=
  ∀ row ∈ rows, Row.Strict row

/-- Every row in the list is nonempty. -/
def RowsNonempty (rows : List Row) : Prop :=
  ∀ row ∈ rows, row ≠ []

/-- No value appears twice anywhere in the tableau. -/
def EntriesNodup (rows : List Row) : Prop :=
  rows.flatten.Nodup

/-- Row lengths are weakly decreasing. -/
def ShapeSorted (rows : List Row) : Prop :=
  (rows.map List.length).SortedGE

/-- Columns are strictly increasing wherever the lower cell exists. -/
def ColumnStrict (rows : List Row) : Prop :=
  ∀ i j, j < (rows.getD (i + 1) []).length → (rows.getD i []).entry j < (rows.getD (i + 1) []).entry j

/-- Two-row version of column strictness. -/
def ColumnStrictTwoRows (upper lower : Row) : Prop :=
  ∀ j, j < lower.length → upper.entry j < lower.entry j

/-- Concrete invariant bundle for RS tableaux. -/
def IsRSTableau (rows : List Row) : Prop :=
  RowsNonempty rows ∧ RowsStrict rows ∧ ShapeSorted rows ∧ ColumnStrict rows

theorem columnStrict_nil : ColumnStrict ([] : List Row) := by
  intro i j hj
  simp at hj

theorem columnStrict_singleton (row : Row) : ColumnStrict [row] := by
  intro i j hj
  cases i <;> simp at hj

theorem columnStrictTwoRows_of_cons_cons {upper lower : Row} {rows : List Row}
    (h : ColumnStrict (upper :: lower :: rows)) :
    ColumnStrictTwoRows upper lower := by
  intro j hj
  simpa [ColumnStrict, ColumnStrictTwoRows, List.getD_cons_zero, List.getD_cons_succ] using h 0 j hj

theorem columnStrict_tail_of_cons_cons {upper lower : Row} {rows : List Row}
    (h : ColumnStrict (upper :: lower :: rows)) :
    ColumnStrict (lower :: rows) := by
  intro i j hj
  simpa [ColumnStrict, List.getD_cons_succ, Nat.add_assoc] using h (i + 1) j hj

theorem columnStrict_cons_cons_iff {upper lower : Row} {rows : List Row} :
    ColumnStrict (upper :: lower :: rows) ↔
      ColumnStrictTwoRows upper lower ∧ ColumnStrict (lower :: rows) := by
  constructor
  · intro h
    exact ⟨columnStrictTwoRows_of_cons_cons h, columnStrict_tail_of_cons_cons h⟩
  · rintro ⟨hpair, htail⟩
    intro i j hj
    cases i with
    | zero =>
        simpa [ColumnStrict, ColumnStrictTwoRows, List.getD_cons_zero, List.getD_cons_succ] using
          hpair j hj
    | succ i =>
        simpa [ColumnStrict, List.getD_cons_succ, Nat.add_assoc] using htail i j hj

theorem shapeSorted_nil : ShapeSorted ([] : List Row) := by
  rw [ShapeSorted, List.sortedGE_iff_pairwise]
  simp

theorem shapeSorted_tail_of_cons {row : Row} {rows : List Row}
    (h : ShapeSorted (row :: rows)) :
    ShapeSorted rows := by
  rw [ShapeSorted, List.sortedGE_iff_pairwise] at h ⊢
  simpa using (List.pairwise_cons.1 h).2

theorem head_ge_all_of_shapeSorted_cons {row : Row} {rows : List Row}
    (h : ShapeSorted (row :: rows)) :
    ∀ r ∈ rows, r.length ≤ row.length := by
  rw [ShapeSorted, List.sortedGE_iff_pairwise] at h
  intro r hr
  exact (List.pairwise_cons.1 h).1 r.length (List.mem_map.2 ⟨r, hr, rfl⟩)

theorem length_head_le_of_shapeSorted_cons_cons {row lower : Row} {rows : List Row}
    (h : ShapeSorted (row :: lower :: rows)) :
    lower.length ≤ row.length := by
  exact head_ge_all_of_shapeSorted_cons h lower (by simp)

theorem shapeSorted_cons_of_head_ge_all {row : Row} {rows : List Row}
    (htail : ShapeSorted rows)
    (hhead : ∀ r ∈ rows, r.length ≤ row.length) :
    ShapeSorted (row :: rows) := by
  rw [ShapeSorted, List.sortedGE_iff_pairwise] at htail ⊢
  refine List.pairwise_cons.2 ?_
  constructor
  · intro n hn
    rcases List.mem_map.1 hn with ⟨r, hr, rfl⟩
    exact hhead r hr
  · exact htail

theorem shapeSorted_cons_cons_of_head_ge {row first : Row} {rows : List Row}
    (hhead : first.length ≤ row.length)
    (htail : ShapeSorted (first :: rows)) :
    ShapeSorted (row :: first :: rows) := by
  apply shapeSorted_cons_of_head_ge_all htail
  intro r hr
  rcases List.mem_cons.1 hr with rfl | hr
  · exact hhead
  · exact le_trans (head_ge_all_of_shapeSorted_cons htail r hr) hhead

theorem rowStrict_singleton (x : ℕ) : RowsStrict [[x]] := by
  intro row hrow
  simp at hrow
  rcases hrow with rfl
  simp [Row.Strict, List.sortedLT_iff_pairwise]

theorem not_mem_row_of_not_mem_flatten {x : ℕ} {row : Row} {rows : List Row}
    (hrow : row ∈ rows) (hx : x ∉ rows.flatten) :
    x ∉ row := by
  intro hxrow
  exact hx (List.mem_flatten_of_mem hrow hxrow)

theorem tail_entriesNodup_of_entriesNodup_cons {row : Row} {rows : List Row}
    (hnd : EntriesNodup (row :: rows)) :
    EntriesNodup rows := by
  have hflat := (List.nodup_flatten).1 hnd
  refine (List.nodup_flatten).2 ?_
  refine ⟨?_, ?_⟩
  · intro r hr
    exact hflat.1 r (by simp [hr])
  · exact (List.pairwise_cons.1 hflat.2).2

theorem disjoint_head_of_entriesNodup_cons {row : Row} {rows : List Row}
    (hnd : EntriesNodup (row :: rows)) :
    ∀ r ∈ rows, List.Disjoint row r := by
  have hflat := (List.nodup_flatten).1 hnd
  exact (List.pairwise_cons.1 hflat.2).1

theorem not_mem_tail_flatten_of_mem_head {y : ℕ} {row : Row} {rows : List Row}
    (hy : y ∈ row) (hnd : EntriesNodup (row :: rows)) :
    y ∉ rows.flatten := by
  intro htail
  rcases List.mem_flatten.1 htail with ⟨r, hr, hyr⟩
  have hdis := disjoint_head_of_entriesNodup_cons hnd r hr
  exact (List.disjoint_left.1 hdis hy hyr)

theorem entriesNodup_insertRows {x : ℕ} {rows : List Row}
    (hnd : EntriesNodup rows) (hx : x ∉ rows.flatten) :
    EntriesNodup (insertRows x rows).rows := by
  rw [EntriesNodup]
  exact (perm_flatten_insertRows x rows).nodup_iff.2 (List.nodup_cons.2 ⟨hx, hnd⟩)

theorem rowsStrict_insertRows {x : ℕ} :
    ∀ {rows : List Row}, RowsStrict rows → EntriesNodup rows → x ∉ rows.flatten →
      RowsStrict (insertRows x rows).rows
  | [], _, _, _ => by
      simpa [insertRows] using rowStrict_singleton x
  | row :: rows, hstrict, hnd, hx => by
      have hxrow : x ∉ row := by
        exact not_mem_row_of_not_mem_flatten (by simp) hx
      cases hb : (Row.insert x row).bumped with
      | none =>
          intro r hr
          rw [insertRows_rows_cons_of_bumped_none hb] at hr
          rcases List.mem_cons.1 hr with rfl | hr
          · exact Row.strict_insert (hstrict row (by simp)) hxrow
          · exact hstrict r (by simp [hr])
      | some y =>
          have hbump : Row.bump? x row = some y := by
            simpa [Row.bumped_insert] using hb
          have hyrow : y ∈ row := Row.mem_of_bump?_eq_some hbump
          have hytail : y ∉ rows.flatten := by
            exact not_mem_tail_flatten_of_mem_head hyrow hnd
          have hstrict_tail : RowsStrict rows := by
            intro r hr
            exact hstrict r (by simp [hr])
          have hnd_tail : EntriesNodup rows := tail_entriesNodup_of_entriesNodup_cons hnd
          intro r hr
          rw [insertRows_rows_cons_of_bumped_some hb] at hr
          rcases List.mem_cons.1 hr with rfl | hr
          · exact Row.strict_insert (hstrict row (by simp)) hxrow
          · exact rowsStrict_insertRows hstrict_tail hnd_tail hytail r hr

theorem lower_bump_exists_of_column {upper lower : Row} {x y : ℕ}
    (hcol : ColumnStrictTwoRows upper lower)
    (hupper : Row.Strict upper) (hx : x ∉ upper) (h : Row.bump? x upper = some y) :
    ∀ {as bs : Row}, upper = as ++ y :: bs → as.length < lower.length →
      ∃ z, Row.bump? y lower = some z
  | as, bs, hup, hlen => by
      have hycol : y < lower.entry as.length := by
        have hyupper : upper.entry as.length = y := by
          rw [hup]
          have hlt : as.length < (as ++ y :: bs).length := by simp
          rw [Row.entry_eq_getElem _ hlt]
          simp
        rw [← hyupper]
        exact hcol as.length hlen
      exact Row.exists_bump?_of_lt_entry hlen hycol

theorem columnStrictTwoRows_insert_upper_of_bump_none {upper lower : Row} {x : ℕ}
    (hcol : ColumnStrictTwoRows upper lower)
    (hlen : lower.length ≤ upper.length)
    (h : Row.bump? x upper = none) :
    ColumnStrictTwoRows (Row.insert x upper).row lower := by
  intro j hj
  have hju : j < upper.length := lt_of_lt_of_le hj hlen
  rw [Row.insert_eq_append_of_bump_none h]
  rw [Row.entry_append_left _ _ hju]
  exact hcol j hj

theorem columnStrictTwoRows_insert_upper_of_bump_some_lower_none
    {upper lower : Row} {x y : ℕ}
    (hcol : ColumnStrictTwoRows upper lower)
    (hupper : Row.Strict upper) (hx : x ∉ upper)
    (h : Row.bump? x upper = some y)
    (hlower : Row.bump? y lower = none) :
    ColumnStrictTwoRows (Row.insert x upper).row (Row.insert y lower).row := by
  rcases Row.insert_eq_append_of_bump hupper hx h with ⟨as, bs, hup, hins, hprefix, hxy⟩
  have hle_as : lower.length ≤ as.length := by
    by_contra hlt
    have hlt' : as.length < lower.length := Nat.lt_of_not_ge hlt
    rcases lower_bump_exists_of_column
        (upper := upper) (lower := lower) (x := x) (y := y)
        hcol hupper hx h hup hlt' with ⟨z, hz⟩
    have : (Row.insert y lower).bumped = some z := by
      simpa [Row.bumped_insert] using hz
    simpa [Row.bumped_insert, hlower] using this
  have hinsLower : (Row.insert y lower).row = lower ++ [y] :=
    Row.insert_eq_append_of_bump_none hlower
  intro j hj
  rw [hinsLower] at hj
  rw [hins, hinsLower]
  have hj' : j < lower.length + 1 := by simpa using hj
  have hjle : j ≤ lower.length := Nat.lt_succ_iff.mp hj'
  rcases lt_or_eq_of_le hjle with hjlt | rfl
  · by_cases hjas : j < as.length
    · rw [Row.entry_append_left _ _ hjlt]
      calc
        (as ++ x :: bs).entry j = as.entry j := by
          exact Row.entry_append_left _ _ hjas
        _ = upper.entry j := by
          rw [hup]
          symm
          exact Row.entry_append_left _ _ hjas
        _ < lower.entry j := hcol j hjlt
    · have hle_j : as.length ≤ j := Nat.le_of_not_gt hjas
      have hjeq : j = as.length := le_antisymm (le_trans hjle hle_as) hle_j
      subst hjeq
      have hlower_same : (lower ++ [y]).entry as.length = lower.entry as.length := by
        exact Row.entry_append_left _ _ hjlt
      rw [hlower_same]
      have hy_upper : upper.entry as.length = y := by
        rw [hup]
        calc
          (as ++ y :: bs).entry as.length = Row.entry (y :: bs) 0 := by
            rw [Row.entry_append_right _ _ (Nat.le_refl _)]
            simp
          _ = y := by simp [Row.entry]
      have hy_lower : y < lower.entry as.length := by
        rw [← hy_upper]
        exact hcol as.length hjlt
      calc
        (as ++ x :: bs).entry as.length = Row.entry (x :: bs) 0 := by
          rw [Row.entry_append_right _ _ (Nat.le_refl _)]
          simp
        _ = x := by simp [Row.entry]
        _ < y := hxy
        _ < lower.entry as.length := hy_lower
  · have hy_last : (lower ++ [y]).entry lower.length = y := by
      calc
        (lower ++ [y]).entry lower.length = Row.entry [y] 0 := by
          rw [Row.entry_append_right _ _ (Nat.le_refl _)]
          simp
        _ = y := by simp [Row.entry]
    rw [hy_last]
    by_cases hltas : lower.length < as.length
    · have hpre : as.entry lower.length < x := by
        have hmem : as.entry lower.length ∈ as := by
          rw [Row.entry_eq_getElem as hltas]
          exact List.getElem_mem hltas
        exact hprefix _ hmem
      calc
        (as ++ x :: bs).entry lower.length = as.entry lower.length := by
          exact Row.entry_append_left _ _ hltas
        _ < x := hpre
        _ < y := hxy
    · have heq : lower.length = as.length := le_antisymm hle_as (Nat.le_of_not_gt hltas)
      calc
        (as ++ x :: bs).entry lower.length = Row.entry (x :: bs) 0 := by
          rw [heq]
          rw [Row.entry_append_right _ _ (Nat.le_refl _)]
          simp
        _ = x := by simp [Row.entry]
        _ < y := hxy

theorem lower_insert_data_le_of_column
    {upper lower : Row} {x y z : ℕ}
    (hcol : ColumnStrictTwoRows upper lower)
    (hupper : Row.Strict upper) (hlowerStrict : Row.Strict lower)
    (hx : x ∉ upper) (hy : y ∉ lower)
    (h : Row.bump? x upper = some y)
    (hlower : Row.bump? y lower = some z) :
    ∀ {as bs : Row}, upper = as ++ y :: bs →
      ∃ cs ds, lower = cs ++ z :: ds ∧
        (Row.insert y lower).row = cs ++ y :: ds ∧
        (∀ a ∈ cs, a < y) ∧
        cs.length ≤ as.length
  | as, bs, hup => by
      rcases Row.insert_eq_append_of_bump hlowerStrict hy hlower with
        ⟨cs, ds, hlow, hinsL, hprefixL, hyz⟩
      refine ⟨cs, ds, hlow, hinsL, hprefixL, ?_⟩
      by_contra hgt
      have hlt : as.length < cs.length := Nat.lt_of_not_ge hgt
      have hy_upper : upper.entry as.length = y := by
        rw [hup]
        calc
          (as ++ y :: bs).entry as.length = Row.entry (y :: bs) 0 := by
            rw [Row.entry_append_right _ _ (Nat.le_refl _)]
            simp
          _ = y := by simp [Row.entry]
      have hy_lt_lower : y < lower.entry as.length := by
        rw [← hy_upper]
        have hlen : as.length < lower.length := by
          rw [hlow]
          simp [List.length_append]
          omega
        exact hcol as.length hlen
      have hlow_eq : lower.entry as.length = cs.entry as.length := by
        rw [hlow]
        exact Row.entry_append_left _ _ hlt
      have hmem : cs.entry as.length ∈ cs := by
        rw [Row.entry_eq_getElem cs hlt]
        exact List.getElem_mem hlt
      have hlt_y : cs.entry as.length < y := hprefixL _ hmem
      rw [hlow_eq] at hy_lt_lower
      exact (Nat.lt_asymm hlt_y hy_lt_lower).elim

theorem columnStrictTwoRows_insert_upper_of_bump_some_lower_some
    {upper lower : Row} {x y z : ℕ}
    (hcol : ColumnStrictTwoRows upper lower)
    (hupper : Row.Strict upper) (hlowerStrict : Row.Strict lower)
    (hx : x ∉ upper) (hy : y ∉ lower)
    (h : Row.bump? x upper = some y)
    (hlower : Row.bump? y lower = some z) :
    ColumnStrictTwoRows (Row.insert x upper).row (Row.insert y lower).row := by
  rcases Row.insert_eq_append_of_bump hupper hx h with ⟨as, bs, hup, hinsU, hprefixU, hxy⟩
  rcases lower_insert_data_le_of_column
      (upper := upper) (lower := lower) (x := x) (y := y) (z := z)
      hcol hupper hlowerStrict hx hy h hlower hup with
    ⟨cs, ds, hlow, hinsL, hprefixL, hcsle⟩
  intro j hj
  have hjins : j < (cs ++ y :: ds).length := by
    simpa [hinsL] using hj
  rw [hinsU, hinsL]
  by_cases hjcs : j < cs.length
  · have hjas : j < as.length := lt_of_lt_of_le hjcs hcsle
    rw [Row.entry_append_left _ _ hjcs]
    calc
      (as ++ x :: bs).entry j = as.entry j := Row.entry_append_left _ _ hjas
      _ = upper.entry j := by
        rw [hup]
        symm
        exact Row.entry_append_left _ _ hjas
      _ < lower.entry j := hcol j (by
        rw [hlow]
        simp [List.length_append]
        omega)
      _ = cs.entry j := by
        rw [hlow]
        exact Row.entry_append_left _ _ hjcs
  · have hjle : cs.length ≤ j := Nat.le_of_not_gt hjcs
    rcases eq_or_lt_of_le hjle with hjeq | hjgt
    · subst hjeq
      have hy_lower : (cs ++ y :: ds).entry cs.length = y := by
        calc
          (cs ++ y :: ds).entry cs.length = Row.entry (y :: ds) 0 := by
            rw [Row.entry_append_right _ _ (Nat.le_refl _)]
            simp
          _ = y := by simp [Row.entry]
      rw [hy_lower]
      by_cases hcas : cs.length < as.length
      · have hpre : as.entry cs.length < x := by
          have hmem : as.entry cs.length ∈ as := by
            rw [Row.entry_eq_getElem as hcas]
            exact List.getElem_mem hcas
          exact hprefixU _ hmem
        calc
          (as ++ x :: bs).entry cs.length = as.entry cs.length := Row.entry_append_left _ _ hcas
          _ < x := hpre
          _ < y := hxy
      · have hceq : cs.length = as.length := le_antisymm hcsle (Nat.le_of_not_gt hcas)
        calc
          (as ++ x :: bs).entry cs.length = Row.entry (x :: bs) 0 := by
            rw [hceq]
            rw [Row.entry_append_right _ _ (Nat.le_refl _)]
            simp
          _ = x := by simp [Row.entry]
          _ < y := hxy
    · have hjlt_lower : j < lower.length := by
        rw [hlow]
        simpa [List.length_append] using hjins
      have hjgt' : cs.length + 1 ≤ j := by omega
      have hlower_same : (cs ++ y :: ds).entry j = lower.entry j := by
        rw [hlow]
        calc
          (cs ++ y :: ds).entry j = Row.entry ds (j - (cs.length + 1)) := by
            rw [Row.entry_append_right _ _ hjle]
            have hk : j - cs.length = j - (cs.length + 1) + 1 := by omega
            rw [hk]
            simp [Row.entry]
          _ = (cs ++ z :: ds).entry j := by
            symm
            rw [Row.entry_append_right _ _ hjle]
            have hk : j - cs.length = j - (cs.length + 1) + 1 := by omega
            rw [hk]
            simp [Row.entry]
      by_cases hjas : j < as.length
      · rw [hlower_same]
        calc
          (as ++ x :: bs).entry j = as.entry j := Row.entry_append_left _ _ hjas
          _ = upper.entry j := by
            rw [hup]
            symm
            exact Row.entry_append_left _ _ hjas
          _ < lower.entry j := hcol j hjlt_lower
      · by_cases hjeqas : j = as.length
        · subst hjeqas
          rw [hlower_same]
          have hy_upper : upper.entry as.length = y := by
            rw [hup]
            calc
              (as ++ y :: bs).entry as.length = Row.entry (y :: bs) 0 := by
                rw [Row.entry_append_right _ _ (Nat.le_refl _)]
                simp
              _ = y := by simp [Row.entry]
          have hy_lower_lt : y < lower.entry as.length := by
            rw [← hy_upper]
            exact hcol as.length hjlt_lower
          calc
            (as ++ x :: bs).entry as.length = Row.entry (x :: bs) 0 := by
              rw [Row.entry_append_right _ _ (Nat.le_refl _)]
              simp
            _ = x := by simp [Row.entry]
            _ < y := hxy
            _ < lower.entry as.length := hy_lower_lt
        · rw [hlower_same]
          have haslt : as.length < j := lt_of_le_of_ne (Nat.le_of_not_gt hjas) (Ne.symm hjeqas)
          calc
            (as ++ x :: bs).entry j = Row.entry bs (j - (as.length + 1)) := by
              rw [Row.entry_append_right _ _ (Nat.le_of_lt haslt)]
              have hk₁ : j - as.length = j - (as.length + 1) + 1 := by omega
              rw [hk₁]
              simp [Row.entry]
            _ = Row.entry (y :: bs) (j - as.length) := by
              have hk₁ : j - as.length = j - (as.length + 1) + 1 := by omega
              rw [hk₁]
              simp [Row.entry]
            _ = upper.entry j := by
              rw [hup]
              symm
              exact Row.entry_append_right _ _ (Nat.le_of_lt haslt)
            _ < lower.entry j := hcol j hjlt_lower

theorem columnStrict_insertRows_of_bumped_none {x : ℕ} {row : Row} {rows : List Row}
    (hb : (Row.insert x row).bumped = none)
    (hshape : ShapeSorted (row :: rows))
    (hcol : ColumnStrict (row :: rows)) :
    ColumnStrict (insertRows x (row :: rows)).rows := by
  have hbump : Row.bump? x row = none := by
    simpa [Row.bumped_insert] using hb
  rw [insertRows_rows_cons_of_bumped_none hb]
  cases rows with
  | nil =>
      simpa using columnStrict_singleton (Row.insert x row).row
  | cons lower tail =>
      have hpair_tail :
          ColumnStrictTwoRows row lower ∧ ColumnStrict (lower :: tail) := by
        simpa using
          (columnStrict_cons_cons_iff (upper := row) (lower := lower) (rows := tail)).1 hcol
      have hlen : lower.length ≤ row.length := by
        exact length_head_le_of_shapeSorted_cons_cons hshape
      apply (columnStrict_cons_cons_iff
        (upper := (Row.insert x row).row) (lower := lower) (rows := tail)).2
      exact ⟨columnStrictTwoRows_insert_upper_of_bump_none hpair_tail.1 hlen hbump, hpair_tail.2⟩

theorem columnStrict_insertRows_of_bumped_some_tail_none
    {x y : ℕ} {row lower : Row} {tail : List Row}
    (hb : (Row.insert x row).bumped = some y)
    (hbl : (Row.insert y lower).bumped = none)
    (hshape : ShapeSorted (row :: lower :: tail))
    (hcol : ColumnStrict (row :: lower :: tail))
    (hstrict : RowsStrict (row :: lower :: tail))
    (hnd : EntriesNodup (row :: lower :: tail))
    (hx : x ∉ (row :: lower :: tail).flatten) :
    ColumnStrict (insertRows x (row :: lower :: tail)).rows := by
  have hbump : Row.bump? x row = some y := by
    simpa [Row.bumped_insert] using hb
  have hylower : Row.bump? y lower = none := by
    simpa [Row.bumped_insert] using hbl
  have hpair_tail :
      ColumnStrictTwoRows row lower ∧ ColumnStrict (lower :: tail) := by
    simpa using
      (columnStrict_cons_cons_iff (upper := row) (lower := lower) (rows := tail)).1 hcol
  have hshape_tail : ShapeSorted (lower :: tail) := shapeSorted_tail_of_cons hshape
  have hstrict_tail : RowsStrict (lower :: tail) := by
    intro r hr
    exact hstrict r (by simp [hr])
  have hnd_tail : EntriesNodup (lower :: tail) := tail_entriesNodup_of_entriesNodup_cons hnd
  have hy_notin_tail : y ∉ (lower :: tail).flatten := by
    have hyrow : y ∈ row := Row.mem_of_bump?_eq_some hbump
    exact not_mem_tail_flatten_of_mem_head hyrow hnd
  have hxrow : x ∉ row := not_mem_row_of_not_mem_flatten (by simp) hx
  rw [insertRows_rows_cons_of_bumped_some hb]
  rw [insertRows_rows_cons_of_bumped_none hbl]
  apply (columnStrict_cons_cons_iff
    (upper := (Row.insert x row).row)
    (lower := (Row.insert y lower).row)
    (rows := tail)).2
  refine ⟨?_, ?_⟩
  · exact columnStrictTwoRows_insert_upper_of_bump_some_lower_none
      hpair_tail.1 (hstrict row (by simp)) hxrow hbump hylower
  · simpa [insertRows_rows_cons_of_bumped_none hbl] using
      (columnStrict_insertRows_of_bumped_none
        (x := y) (row := lower) (rows := tail) hbl hshape_tail hpair_tail.2)

theorem columnStrict_insertRows_singleton {x : ℕ} {row : Row}
    (hstrict : Row.Strict row) (hx : x ∉ row) :
    ColumnStrict (insertRows x [row]).rows := by
  cases hb : (Row.insert x row).bumped with
  | none =>
      exact columnStrict_insertRows_of_bumped_none hb
        (by simp [ShapeSorted, List.sortedGE_iff_pairwise])
        (columnStrict_singleton row)
  | some y =>
      have hbump : Row.bump? x row = some y := by
        simpa [Row.bumped_insert] using hb
      have hbnil : Row.bump? y ([] : Row) = none := by simp [Row.bump?]
      rw [insertRows_rows_cons_of_bumped_some hb]
      rw [show insertRows y [] = ⟨[[y]], 0⟩ by rfl]
      apply (columnStrict_cons_cons_iff
        (upper := (Row.insert x row).row) (lower := [y]) (rows := [])).2
      refine ⟨?_, columnStrict_singleton [y]⟩
      exact columnStrictTwoRows_insert_upper_of_bump_some_lower_none
        (upper := row) (lower := []) (x := x) (y := y)
        (by intro j hj; simp at hj)
        hstrict hx hbump hbnil

theorem shapeSorted_insertRows {x : ℕ} :
    ∀ {rows : List Row}, ShapeSorted rows → ColumnStrict rows → RowsStrict rows →
      EntriesNodup rows → x ∉ rows.flatten → ShapeSorted (insertRows x rows).rows
  | [], _, _, _, _, _ => by
      simp [insertRows, ShapeSorted, List.sortedGE_iff_pairwise]
  | row :: rows, hshape, hcol, hstrict, hnd, hx => by
      have hxrow : x ∉ row := not_mem_row_of_not_mem_flatten (by simp) hx
      cases hb : (Row.insert x row).bumped with
      | none =>
          rw [insertRows_rows_cons_of_bumped_none hb]
          apply shapeSorted_cons_of_head_ge_all
          · exact shapeSorted_tail_of_cons hshape
          ·
            have hhead : ∀ r ∈ rows, r.length ≤ row.length := head_ge_all_of_shapeSorted_cons hshape
            intro r hr
            have hle : r.length ≤ row.length := hhead r hr
            have hbump : Row.bump? x row = none := by
              simpa [Row.bumped_insert] using hb
            have hlen : (Row.insert x row).row.length = row.length + 1 :=
              Row.length_insert_of_bump_none (row := row) (x := x) hbump
            rw [hlen]
            omega
      | some y =>
          have hbump : Row.bump? x row = some y := by
            simpa [Row.bumped_insert] using hb
          have hyrow : y ∈ row := Row.mem_of_bump?_eq_some hbump
          have hytail : y ∉ rows.flatten := not_mem_tail_flatten_of_mem_head hyrow hnd
          have hstrict_tail : RowsStrict rows := by
            intro r hr
            exact hstrict r (by simp [hr])
          have hnd_tail : EntriesNodup rows := tail_entriesNodup_of_entriesNodup_cons hnd
          have hshape_tail : ShapeSorted rows := shapeSorted_tail_of_cons hshape
          rw [insertRows_rows_cons_of_bumped_some hb]
          cases rows with
          | nil =>
              have hlen : (Row.insert x row).row.length = row.length := by
                exact Row.length_insert_of_bump_some (row := row) (x := x) hbump
              have hrowpos : 1 ≤ row.length := by
                cases row with
                | nil => simp [Row.bump?, Row.bump?] at hbump
                | cons a t => simp
              rw [show insertRows y [] = ⟨[[y]], 0⟩ by rfl]
              simpa [ShapeSorted, hlen, List.sortedGE_iff_pairwise] using hrowpos
          | cons lower tail =>
              have hcol_pair_tail : ColumnStrictTwoRows row lower ∧ ColumnStrict (lower :: tail) := by
                simpa using (columnStrict_cons_cons_iff
                  (upper := row) (lower := lower) (rows := tail)).1 hcol
              have hcol_pair : ColumnStrictTwoRows row lower := hcol_pair_tail.1
              have hcol_tail : ColumnStrict (lower :: tail) := hcol_pair_tail.2
              have htail_sorted :
                  ShapeSorted (insertRows y (lower :: tail)).rows :=
                shapeSorted_insertRows hshape_tail hcol_tail hstrict_tail hnd_tail hytail
              have hheadlen : lower.length ≤ row.length :=
                length_head_le_of_shapeSorted_cons_cons hshape
              have hlenRow : (Row.insert x row).row.length = row.length := by
                exact Row.length_insert_of_bump_some (row := row) (x := x) hbump
              cases hbl : (Row.insert y lower).bumped with
              | none =>
                  have hylower : y ∉ lower := not_mem_row_of_not_mem_flatten (by simp) hytail
                  have ⟨as, bs, hup, _, _, _⟩ :=
                    Row.insert_eq_append_of_bump (hstrict row (by simp)) hxrow hbump
                  have hnotlt : ¬ as.length < lower.length := by
                    intro hlt
                    rcases lower_bump_exists_of_column
                        (upper := row) (lower := lower) (x := x) (y := y)
                        hcol_pair
                        (hstrict row (by simp)) hxrow hbump hup hlt with
                      ⟨z, hz⟩
                    have : (Row.insert y lower).bumped = some z := by
                      simpa [Row.bumped_insert] using hz
                    rw [hbl] at this
                    cases this
                  have hle_as : lower.length ≤ as.length := Nat.le_of_not_gt hnotlt
                  have hlenLower : (Row.insert y lower).row.length = lower.length + 1 := by
                    have hbn : Row.bump? y lower = none := by
                      simpa [Row.bumped_insert] using hbl
                    exact Row.length_insert_of_bump_none (row := lower) (x := y) hbn
                  have hbound : (Row.insert y lower).row.length ≤ (Row.insert x row).row.length := by
                    have hlenRow' : row.length = as.length + 1 + bs.length := by
                      rw [hup]
                      simp [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                    have hrow_ge_as : as.length + 1 ≤ row.length := by
                      rw [hlenRow']
                      omega
                    have hrow_ge_lower : lower.length + 1 ≤ row.length := by
                      omega
                    rw [hlenLower, hlenRow]
                    exact hrow_ge_lower
                  rw [insertRows_rows_cons_of_bumped_none hbl] at htail_sorted ⊢
                  exact shapeSorted_cons_cons_of_head_ge hbound htail_sorted
              | some z =>
                  have hlenLower : (Row.insert y lower).row.length = lower.length := by
                    have hbz : Row.bump? y lower = some z := by
                      simpa [Row.bumped_insert] using hbl
                    exact Row.length_insert_of_bump_some (row := lower) (x := y) hbz
                  have hbound : (Row.insert y lower).row.length ≤ (Row.insert x row).row.length := by
                    rw [hlenLower, hlenRow]
                    exact hheadlen
                  rw [insertRows_rows_cons_of_bumped_some hbl] at htail_sorted ⊢
                  exact shapeSorted_cons_cons_of_head_ge hbound htail_sorted

theorem isRSTableau_insertRows_of_bumped_none {x : ℕ} {row : Row} {rows : List Row}
    (hT : IsRSTableau (row :: rows))
    (hnd : EntriesNodup (row :: rows))
    (hx : x ∉ (row :: rows).flatten)
    (hb : (Row.insert x row).bumped = none) :
    IsRSTableau (insertRows x (row :: rows)).rows := by
  rcases hT with ⟨hnonempty, hstrict, hshape, hcol⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro r hr
    exact rows_nonempty_insertRows x hnonempty r hr
  ·
    exact rowsStrict_insertRows hstrict hnd hx
  ·
    exact shapeSorted_insertRows hshape hcol hstrict hnd hx
  ·
    exact columnStrict_insertRows_of_bumped_none hb hshape hcol

theorem isRSTableau_insertRows_of_bumped_some_tail_none
    {x y : ℕ} {row lower : Row} {tail : List Row}
    (hT : IsRSTableau (row :: lower :: tail))
    (hnd : EntriesNodup (row :: lower :: tail))
    (hx : x ∉ (row :: lower :: tail).flatten)
    (hb : (Row.insert x row).bumped = some y)
    (hbl : (Row.insert y lower).bumped = none) :
    IsRSTableau (insertRows x (row :: lower :: tail)).rows := by
  rcases hT with ⟨hnonempty, hstrict, hshape, hcol⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro r hr
    exact rows_nonempty_insertRows x hnonempty r hr
  ·
    exact rowsStrict_insertRows hstrict hnd hx
  ·
    exact shapeSorted_insertRows hshape hcol hstrict hnd hx
  ·
    exact columnStrict_insertRows_of_bumped_some_tail_none hb hbl hshape hcol hstrict hnd hx

theorem columnStrict_insertRows {x : ℕ} :
    ∀ {rows : List Row}, ShapeSorted rows → ColumnStrict rows → RowsStrict rows →
      EntriesNodup rows → x ∉ rows.flatten → ColumnStrict (insertRows x rows).rows
  | [], _, _, _, _, _ => by
      simpa [insertRows] using columnStrict_singleton [x]
  | row :: rows, hshape, hcol, hstrict, hnd, hx => by
      have hxrow : x ∉ row := not_mem_row_of_not_mem_flatten (by simp) hx
      cases hb : (Row.insert x row).bumped with
      | none =>
          exact columnStrict_insertRows_of_bumped_none hb hshape hcol
      | some y =>
          have hbump : Row.bump? x row = some y := by
            simpa [Row.bumped_insert] using hb
          cases rows with
          | nil =>
              exact columnStrict_insertRows_singleton (hstrict row (by simp)) hxrow
          | cons lower tail =>
              have hpair_tail :
                  ColumnStrictTwoRows row lower ∧ ColumnStrict (lower :: tail) := by
                simpa using
                  (columnStrict_cons_cons_iff (upper := row) (lower := lower) (rows := tail)).1 hcol
              have hshape_tail : ShapeSorted (lower :: tail) := shapeSorted_tail_of_cons hshape
              have hstrict_tail : RowsStrict (lower :: tail) := by
                intro r hr
                exact hstrict r (by simp [hr])
              have hnd_tail : EntriesNodup (lower :: tail) := tail_entriesNodup_of_entriesNodup_cons hnd
              have hy_notin_tail : y ∉ (lower :: tail).flatten := by
                have hyrow : y ∈ row := Row.mem_of_bump?_eq_some hbump
                exact not_mem_tail_flatten_of_mem_head hyrow hnd
              have hy_notin_lower : y ∉ lower := not_mem_row_of_not_mem_flatten (by simp) hy_notin_tail
              rw [insertRows_rows_cons_of_bumped_some hb]
              cases hbl : (Row.insert y lower).bumped with
              | none =>
                  simpa [insertRows_rows_cons_of_bumped_some hb] using
                    (columnStrict_insertRows_of_bumped_some_tail_none
                      hb hbl hshape hcol hstrict hnd hx)
              | some z =>
                  have htail :
                      ColumnStrict (insertRows y (lower :: tail)).rows :=
                    columnStrict_insertRows hshape_tail hpair_tail.2 hstrict_tail hnd_tail hy_notin_tail
                  rw [insertRows_rows_cons_of_bumped_some hbl] at htail
                  rw [insertRows_rows_cons_of_bumped_some hbl]
                  apply (columnStrict_cons_cons_iff
                    (upper := (Row.insert x row).row)
                    (lower := (Row.insert y lower).row)
                    (rows := (insertRows z tail).rows)).2
                  refine ⟨?_, htail⟩
                  have hblow : Row.bump? y lower = some z := by
                    simpa [Row.bumped_insert] using hbl
                  exact columnStrictTwoRows_insert_upper_of_bump_some_lower_some
                    hpair_tail.1
                    (hstrict row (by simp))
                    (hstrict lower (by simp))
                    hxrow hy_notin_lower hbump hblow

theorem isRSTableau_insertRows {x : ℕ} {rows : List Row}
    (hT : IsRSTableau rows)
    (hnd : EntriesNodup rows)
    (hx : x ∉ rows.flatten) :
    IsRSTableau (insertRows x rows).rows := by
  rcases hT with ⟨hnonempty, hstrict, hshape, hcol⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    exact rows_nonempty_insertRows x hnonempty r hr
  · exact rowsStrict_insertRows hstrict hnd hx
  · exact shapeSorted_insertRows hshape hcol hstrict hnd hx
  · exact columnStrict_insertRows hshape hcol hstrict hnd hx

end RS
