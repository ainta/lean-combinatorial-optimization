import Mathlib.Combinatorics.Young.SemistandardTableau
import Mathlib.Data.List.GetD

/-!
# Internal tableaux for Robinson-Schensted

This file introduces a concrete tableau representation intended for the Robinson-Schensted
development. The actual insertion algorithm will use list-based rows; the connection to
`YoungDiagram` is established here so later files can talk about shapes without switching
representations.
-/

namespace RS

abbrev Row := List ℕ

namespace Row

/-- Concrete row access with zero as the out-of-bounds default. -/
def entry (row : Row) (j : ℕ) : ℕ :=
  row.getD j 0

@[simp]
theorem entry_eq_zero_of_length_le (row : Row) {j : ℕ} (hj : row.length ≤ j) :
    row.entry j = 0 := by
  simp [entry, hj]

@[simp]
theorem entry_eq_getElem (row : Row) {j : ℕ} (hj : j < row.length) :
    row.entry j = row[j] := by
  simp [entry, hj]

theorem entry_append_left (row₁ row₂ : Row) {j : ℕ} (hj : j < row₁.length) :
    (row₁ ++ row₂).entry j = row₁.entry j := by
  simpa [entry] using (List.getD_append row₁ row₂ 0 j hj)

theorem entry_append_right (row₁ row₂ : Row) {j : ℕ} (hj : row₁.length ≤ j) :
    (row₁ ++ row₂).entry j = row₂.entry (j - row₁.length) := by
  simpa [entry] using (List.getD_append_right row₁ row₂ 0 j hj)

end Row

/-- Concrete tableau data for the Robinson-Schensted development.

The initial RS layer only needs list-based rows together with shape invariants:
- each row is nonempty
- row lengths are weakly decreasing
- each row is weakly increasing

Column-strictness is postponed to the insertion layer, where it is more natural to state and use
the local bumping invariants. -/
structure PreTableau where
  rows : List Row
  rows_nonempty : ∀ row ∈ rows, row ≠ []
  row_weak : ∀ row ∈ rows, List.IsChain (· ≤ ·) row
  shape_sorted : (rows.map List.length).SortedGE

namespace PreTableau

/-- Tableau entry with zero outside the listed rows and columns. -/
def entry (T : PreTableau) (i j : ℕ) : ℕ :=
  (T.rows.getD i []).entry j

def shape (T : PreTableau) : List ℕ :=
  T.rows.map List.length

@[simp]
theorem shape_eq_map_length (T : PreTableau) : T.shape = T.rows.map List.length :=
  rfl

@[simp]
theorem mem_shape_iff {T : PreTableau} {n : ℕ} :
    n ∈ T.shape ↔ ∃ row ∈ T.rows, row.length = n := by
  simp [shape]

theorem pos_of_mem_shape (T : PreTableau) {n : ℕ} (hn : n ∈ T.shape) : 0 < n := by
  rcases (mem_shape_iff.mp hn) with ⟨row, hrow, rfl⟩
  cases row with
  | nil =>
      exact (T.rows_nonempty [] hrow rfl).elim
  | cons a tail =>
      simp

theorem shape_sorted_prop (T : PreTableau) : T.shape.SortedGE := by
  simpa [shape] using T.shape_sorted

/-- The Young diagram determined by the row lengths of a concrete tableau. -/
def youngDiagram (T : PreTableau) : YoungDiagram :=
  YoungDiagram.ofRowLens T.shape T.shape_sorted_prop

@[simp]
theorem rowLens_youngDiagram (T : PreTableau) : T.youngDiagram.rowLens = T.shape :=
  YoungDiagram.rowLens_ofRowLens_eq_self (fun x hx => T.pos_of_mem_shape (n := x) hx)

@[simp]
theorem length_shape_eq_length_rows (T : PreTableau) : T.shape.length = T.rows.length := by
  simp [shape]

@[simp]
theorem length_rowLens_youngDiagram (T : PreTableau) :
    T.youngDiagram.rowLens.length = T.rows.length := by
  rw [T.rowLens_youngDiagram, T.length_shape_eq_length_rows]

@[simp]
theorem entry_eq_zero_of_row_length_le (T : PreTableau) {i : ℕ} (hi : T.rows.length ≤ i) {j : ℕ} :
    T.entry i j = 0 := by
  simp [entry, hi]

@[simp]
theorem entry_eq_zero_of_col_length_le (T : PreTableau) {i j : ℕ}
    (hj : (T.rows.getD i []).length ≤ j) : T.entry i j = 0 := by
  exact Row.entry_eq_zero_of_length_le _ hj

end PreTableau

end RS
