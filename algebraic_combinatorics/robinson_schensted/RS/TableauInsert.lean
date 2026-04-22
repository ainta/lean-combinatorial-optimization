import RS.RowInsert

/-!
# Tableau insertion on row lists

This file implements row-by-row propagation of a bumped entry through a list of rows. The current
results focus on shape growth and basic structural invariants; full tableau correctness is the next
layer.
-/

namespace RS

/-- Total number of cells in a list of rows. -/
def cellCount (rows : List Row) : ℕ :=
  (rows.map List.length).sum

structure RowsInsertResult where
  rows : List Row
  newRow : ℕ

/-- Insert `x` into a list of rows, returning the new rows and the index of the row where the new
cell is created. -/
def insertRows (x : ℕ) : List Row → RowsInsertResult
  | [] => ⟨[[x]], 0⟩
  | row :: rows =>
      match Row.insert x row with
      | ⟨row', none⟩ => ⟨row' :: rows, 0⟩
      | ⟨row', some y⟩ =>
          let s := insertRows y rows
          ⟨row' :: s.rows, s.newRow + 1⟩

@[simp]
theorem cellCount_nil : cellCount ([] : List Row) = 0 := by
  rfl

@[simp]
theorem cellCount_cons (row : Row) (rows : List Row) :
    cellCount (row :: rows) = row.length + cellCount rows := by
  simp [cellCount, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem insertRows_rows_cons_of_bumped_none {x : ℕ} {row : Row} {rows : List Row}
    (hb : (Row.insert x row).bumped = none) :
    (insertRows x (row :: rows)).rows = (Row.insert x row).row :: rows := by
  cases hri : Row.insert x row with
  | mk row' bumped =>
      cases bumped with
      | none =>
          simp at hb
          simpa [insertRows, hri]
      | some y =>
          simpa [hri] using hb

theorem insertRows_rows_cons_of_bumped_some {x : ℕ} {row : Row} {rows : List Row} {y : ℕ}
    (hb : (Row.insert x row).bumped = some y) :
    (insertRows x (row :: rows)).rows = (Row.insert x row).row :: (insertRows y rows).rows := by
  cases hri : Row.insert x row with
  | mk row' bumped =>
      cases bumped with
      | none =>
          simpa [hri] using hb
      | some y' =>
          have hy : y' = y := by simpa [hri] using hb
          subst hy
          simpa [insertRows, hri]

theorem cellCount_insertRows (x : ℕ) :
    ∀ rows : List Row, cellCount ((insertRows x rows).rows) = cellCount rows + 1
  | [] => by
      simp [insertRows, cellCount]
  | row :: rows => by
      cases hb : (Row.insert x row).bumped with
      | none =>
          have hbump : Row.bump? x row = none := by
            simpa [Row.bumped_insert] using hb
          have hlen := Row.length_insert_of_bump_none (row := row) (x := x) hbump
          calc
            cellCount ((insertRows x (row :: rows)).rows)
                = cellCount ((Row.insert x row).row :: rows) := by
                    rw [insertRows_rows_cons_of_bumped_none hb]
            _ = (Row.insert x row).row.length + cellCount rows := cellCount_cons _ _
            _ = (row.length + 1) + cellCount rows := by rw [hlen]
            _ = cellCount (row :: rows) + 1 := by
              rw [cellCount_cons]
              omega
      | some y =>
          have hbump : Row.bump? x row = some y := by
            simpa [Row.bumped_insert] using hb
          have hlen := Row.length_insert_of_bump_some (row := row) (x := x) hbump
          calc
            cellCount ((insertRows x (row :: rows)).rows)
                = cellCount ((Row.insert x row).row :: (insertRows y rows).rows) := by
                    rw [insertRows_rows_cons_of_bumped_some hb]
            _ = (Row.insert x row).row.length + cellCount ((insertRows y rows).rows) :=
                  cellCount_cons _ _
            _ = row.length + (cellCount rows + 1) := by rw [hlen, cellCount_insertRows]
            _ = cellCount (row :: rows) + 1 := by
              rw [cellCount_cons]
              omega

theorem rows_nonempty_insertRows (x : ℕ) :
    ∀ {rows : List Row}, (∀ row ∈ rows, row ≠ []) →
      ∀ row ∈ (insertRows x rows).rows, row ≠ []
  | [], _, row, hrow => by
      simp [insertRows] at hrow
      rcases hrow with rfl
      simp
  | row₀ :: rows, hnonempty, row, hrow => by
      cases hb : (Row.insert x row₀).bumped with
      | none =>
          rw [insertRows_rows_cons_of_bumped_none hb] at hrow
          have hrow' : row ∈ (Row.insert x row₀).row :: rows := hrow
          rcases List.mem_cons.1 hrow' with rfl | hrow'
          ·
            intro hnil
            have hpos : 0 < (Row.insert x row₀).row.length := Row.length_pos_insert x row₀
            have : 0 < 0 := by simpa [hnil] using hpos
            exact (Nat.lt_irrefl 0) this
          · exact hnonempty _ (by simp [hrow'])
      | some y =>
          rw [insertRows_rows_cons_of_bumped_some hb] at hrow
          have hrow' : row ∈ (Row.insert x row₀).row :: (insertRows y rows).rows := hrow
          rcases List.mem_cons.1 hrow' with rfl | hrow'
          ·
            intro hnil
            have hpos : 0 < (Row.insert x row₀).row.length := Row.length_pos_insert x row₀
            have : 0 < 0 := by simpa [hnil] using hpos
            exact (Nat.lt_irrefl 0) this
          ·
            have htail_nonempty : ∀ r ∈ rows, r ≠ [] := by
              intro r hr
              exact hnonempty r (by simp [hr])
            exact rows_nonempty_insertRows _ htail_nonempty _ hrow'

theorem newRow_lt_length_insertRows (x : ℕ) :
    ∀ rows : List Row, (insertRows x rows).newRow < (insertRows x rows).rows.length
  | [] => by
      simp [insertRows]
  | row :: rows => by
      cases hri : Row.insert x row with
      | mk row' bumped =>
          cases bumped with
          | none =>
              simp [insertRows, hri]
          | some y =>
              have ih := newRow_lt_length_insertRows y rows
              simpa [insertRows, hri] using Nat.succ_lt_succ ih

theorem newRow_le_length_insertRows (x : ℕ) :
    ∀ rows : List Row, (insertRows x rows).newRow ≤ rows.length
  | [] => by
      simp [insertRows]
  | row :: rows => by
      cases hri : Row.insert x row with
      | mk row' bumped =>
          cases bumped with
          | none =>
              simp [insertRows, hri]
          | some y =>
              have ih := newRow_le_length_insertRows y rows
              simpa [insertRows, hri] using Nat.succ_le_succ ih

theorem rowLength_newRow_insertRows (x : ℕ) :
    ∀ rows : List Row,
      ((insertRows x rows).rows.getD (insertRows x rows).newRow []).length =
        (rows.getD (insertRows x rows).newRow []).length + 1
  | [] => by
      simp [insertRows]
  | row :: rows => by
      cases hri : Row.insert x row with
      | mk row' bumped =>
          cases bumped with
          | none =>
              have hbump : Row.bump? x row = none := by
                simpa [Row.bumped_insert] using congrArg Row.InsertResult.bumped hri
              have hlen := Row.length_insert_of_bump_none (row := row) (x := x) hbump
              have hlen' : row'.length = row.length + 1 := by
                simpa [hri] using hlen
              simpa [insertRows, hri, List.getD_cons_zero] using hlen'
          | some y =>
              have ih := rowLength_newRow_insertRows y rows
              rw [insertRows, hri, List.getD_cons_succ, List.getD_cons_succ]
              simpa [Nat.add_comm] using ih

theorem perm_flatten_insertRows (x : ℕ) :
    ∀ rows : List Row, List.Perm ((insertRows x rows).rows.flatten) (x :: rows.flatten)
  | [] => by
      simp [insertRows]
  | row :: rows => by
      cases hb : (Row.insert x row).bumped with
      | none =>
          rw [insertRows_rows_cons_of_bumped_none hb]
          have hbump : Row.bump? x row = none := by
            simpa [Row.bumped_insert] using hb
          have hperm : List.Perm ((Row.insert x row).row ++ rows.flatten) ((x :: row) ++ rows.flatten) := by
            simpa [hbump, List.append_assoc] using (Row.perm_insert_bumped x row).append_right rows.flatten
          simpa [List.flatten]
      | some y =>
          rw [insertRows_rows_cons_of_bumped_some hb]
          have hbump : Row.bump? x row = some y := by
            simpa [Row.bumped_insert] using hb
          have htail : List.Perm
              ((Row.insert x row).row ++ (insertRows y rows).rows.flatten)
              ((Row.insert x row).row ++ (y :: rows.flatten)) := by
            exact (perm_flatten_insertRows y rows).append_left ((Row.insert x row).row)
          have hrow : List.Perm
              ((Row.insert x row).row ++ (y :: rows.flatten))
              ((x :: row) ++ rows.flatten) := by
            simpa [hbump, List.append_assoc] using (Row.perm_insert_bumped x row).append_right rows.flatten
          exact (by
            simpa [List.flatten, List.append_assoc] using htail.trans hrow)

end RS
