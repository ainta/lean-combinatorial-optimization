import RS.RSTableau

/-!
# Forward Robinson-Schensted correspondence

This file introduces the forward RS construction on words of natural numbers, together with the
basic shape theorem showing that the insertion and recording tableaux evolve with the same shape.
-/

namespace RS

/-- Bump the `i`-th row length by one, appending a new bottom row when `i` is exactly the current
number of rows. -/
def bumpAt : ℕ → List ℕ → List ℕ
  | 0, [] => [1]
  | 0, n :: ns => (n + 1) :: ns
  | i + 1, [] => []
  | i + 1, n :: ns => n :: bumpAt i ns

/-- Add the label `k` to the recording tableau row indexed by `i`. When `i` is the current number
of rows, this creates a new singleton bottom row. -/
def recordAt (k : ℕ) : ℕ → List Row → List Row
  | 0, [] => [[k]]
  | 0, row :: rows => (row ++ [k]) :: rows
  | i + 1, [] => []
  | i + 1, row :: rows => row :: recordAt k i rows

/-- Every tableau entry is strictly smaller than `n`. -/
def EntriesLt (n : ℕ) (rows : List Row) : Prop :=
  ∀ row ∈ rows, ∀ x ∈ row, x < n

theorem rowStrict_append_singleton {row : Row} {k : ℕ}
    (hrow : Row.Strict row) (hk : ∀ x ∈ row, x < k) :
    Row.Strict (row ++ [k]) := by
  rw [Row.Strict, List.sortedLT_iff_pairwise] at hrow ⊢
  rw [List.pairwise_append]
  refine ⟨hrow, by simp, ?_⟩
  intro a ha b hb
  simp only [List.mem_singleton] at hb
  subst b
  exact hk a ha

theorem entriesLt_recordAt (k : ℕ) :
    ∀ i : ℕ, ∀ rows : List Row, EntriesLt k rows → EntriesLt (k + 1) (recordAt k i rows)
  | 0, [], _ => by
      intro row hrow x hx
      simp [recordAt] at hrow
      rcases hrow with rfl
      simp at hx
      rcases hx with rfl
      simp
  | 0, row :: rows, hlt => by
      intro r hr x hx
      simp [recordAt] at hr
      rcases hr with rfl | hr
      · simp [recordAt] at hx
        rcases hx with hx | rfl
        · exact Nat.lt_succ_of_lt (hlt row (by simp) x hx)
        · simp
      · exact Nat.lt_succ_of_lt (hlt r (by simp [hr]) x hx)
  | i + 1, [], _ => by
      intro row hrow
      simp [recordAt] at hrow
  | i + 1, row :: rows, hlt => by
      intro r hr x hx
      simp [recordAt] at hr
      rcases hr with rfl | hr
      · exact Nat.lt_succ_of_lt (hlt r (by simp) x hx)
      ·
        have hlt_tail : EntriesLt k rows := by
          intro r hr' x hx'
          exact hlt r (by simp [hr']) x hx'
        exact entriesLt_recordAt k i rows hlt_tail r hr x hx

theorem rowsStrict_recordAt (k : ℕ) :
    ∀ i : ℕ, ∀ rows : List Row, RowsStrict rows → EntriesLt k rows → RowsStrict (recordAt k i rows)
  | 0, [], _, _ => by
      intro row hrow
      simp [recordAt] at hrow
      rcases hrow with rfl
      simp [Row.Strict, List.sortedLT_iff_pairwise]
  | 0, row :: rows, hstrict, hlt => by
      intro r hr
      simp [recordAt] at hr
      rcases hr with rfl | hr
      · apply rowStrict_append_singleton
        · exact hstrict row (by simp)
        · intro x hx
          exact hlt row (by simp) x hx
      · exact hstrict r (by simp [hr])
  | i + 1, [], _, _ => by
      intro row hrow
      simp [recordAt] at hrow
  | i + 1, row :: rows, hstrict, hlt => by
      intro r hr
      simp [recordAt] at hr
      rcases hr with rfl | hr
      · exact hstrict r (by simp)
      ·
        have hstrict_tail : RowsStrict rows := by
          intro r hr'
          exact hstrict r (by simp [hr'])
        have hlt_tail : EntriesLt k rows := by
          intro r hr' x hx'
          exact hlt r (by simp [hr']) x hx'
        exact rowsStrict_recordAt k i rows hstrict_tail hlt_tail r hr

theorem rowsNonempty_recordAt (k : ℕ) :
    ∀ i : ℕ, ∀ rows : List Row, RowsNonempty rows → i ≤ rows.length → RowsNonempty (recordAt k i rows)
  | 0, [], _, _ => by
      intro row hrow
      simp [recordAt] at hrow
      rcases hrow with rfl
      simp
  | 0, row :: rows, hnonempty, _ => by
      intro r hr
      simp [recordAt] at hr
      rcases hr with rfl | hr
      · simp
      · exact hnonempty r (by simp [hr])
  | i + 1, [], _, hi => by
      cases hi
  | i + 1, row :: rows, hnonempty, hi => by
      intro r hr
      simp [recordAt] at hr
      rcases hr with rfl | hr
      · exact hnonempty r (by simp)
      ·
        have htail : RowsNonempty rows := by
          intro r hr'
          exact hnonempty r (by simp [hr'])
        exact rowsNonempty_recordAt k i rows htail (Nat.le_of_succ_le_succ hi) r hr

theorem entry_lt_of_entriesLt {k : ℕ} {rows : List Row} {row : Row} {j : ℕ}
    (hlt : EntriesLt k rows) (hrow : row ∈ rows) (hj : j < row.length) :
    row.entry j < k := by
  rw [Row.entry_eq_getElem row hj]
  exact hlt row hrow row[j] (List.getElem_mem hj)

theorem columnStrict_recordAt (k : ℕ) :
    ∀ i : ℕ, ∀ rows : List Row,
      RowsNonempty rows → ShapeSorted rows → ColumnStrict rows → EntriesLt k rows →
      ShapeSorted (recordAt k i rows) → ColumnStrict (recordAt k i rows)
  | 0, [], _, _, _, _, _ => by
      simpa [recordAt] using columnStrict_singleton [k]
  | 0, [row], _, _, _, _, _ => by
      simpa [recordAt] using columnStrict_singleton (row ++ [k])
  | 0, row :: lower :: tail, hnonempty, hshape, hcol, _, _ => by
      rw [recordAt]
      have hpair_tail :
          ColumnStrictTwoRows row lower ∧ ColumnStrict (lower :: tail) := by
        simpa using (columnStrict_cons_cons_iff (upper := row) (lower := lower) (rows := tail)).1 hcol
      apply (columnStrict_cons_cons_iff
        (upper := row ++ [k]) (lower := lower) (rows := tail)).2
      refine ⟨?_, hpair_tail.2⟩
      intro j hj
      have hlen : lower.length ≤ row.length := length_head_le_of_shapeSorted_cons_cons hshape
      have hjrow : j < row.length := lt_of_lt_of_le hj hlen
      calc
        (row ++ [k]).entry j = row.entry j := Row.entry_append_left _ _ hjrow
        _ < lower.entry j := hpair_tail.1 j hj
  | i + 1, [], _, _, _, _, _ => by
      simp [recordAt]
      exact columnStrict_nil
  | i + 1, [row], hnonempty, _, _, hlt, hshape' => by
      cases i with
      | zero =>
          rw [recordAt]
          apply (columnStrict_cons_cons_iff
            (upper := row) (lower := [k]) (rows := [])).2
          refine ⟨?_, columnStrict_singleton [k]⟩
          intro j hj
          have hj0 : j < 1 := by simpa using hj
          have hj0' : j = 0 := by omega
          subst hj0'
          have hrowne : row ≠ [] := hnonempty row (by simp)
          have hshape'' : ShapeSorted [row, [k]] := by simpa [recordAt] using hshape'
          have hlen : 1 ≤ row.length := length_head_le_of_shapeSorted_cons_cons hshape''
          have hjrow : 0 < row.length := by omega
          simpa [Row.entry] using entry_lt_of_entriesLt hlt (by simp) hjrow
      | succ i =>
          simp [recordAt]
          exact columnStrict_singleton row
  | i + 1, row :: lower :: tail, hnonempty, hshape, hcol, hlt, hshape' => by
      cases i with
      | zero =>
          rw [recordAt]
          have hpair_tail :
              ColumnStrictTwoRows row lower ∧ ColumnStrict (lower :: tail) := by
            simpa using (columnStrict_cons_cons_iff (upper := row) (lower := lower) (rows := tail)).1 hcol
          have hnonempty_tail : RowsNonempty (lower :: tail) := by
            intro r hr
            exact hnonempty r (by simp [hr])
          have hshape_tail : ShapeSorted (lower :: tail) := shapeSorted_tail_of_cons hshape
          have hlt_tail : EntriesLt k (lower :: tail) := by
            intro r hr x hx
            exact hlt r (by simp [hr]) x hx
          have hshape'_tail : ShapeSorted (recordAt k 0 (lower :: tail)) := by
            simpa [recordAt] using shapeSorted_tail_of_cons hshape'
          apply (columnStrict_cons_cons_iff
            (upper := row) (lower := lower ++ [k]) (rows := tail)).2
          refine ⟨?_, columnStrict_recordAt k 0 (lower :: tail)
            hnonempty_tail hshape_tail hpair_tail.2 hlt_tail hshape'_tail⟩
          intro j hj
          have hj' : j < lower.length + 1 := by simpa using hj
          have hjle : j ≤ lower.length := Nat.lt_succ_iff.mp hj'
          rcases lt_or_eq_of_le hjle with hjlt | rfl
          · have hlen : lower.length ≤ row.length := length_head_le_of_shapeSorted_cons_cons hshape
            have hjrow : j < row.length := lt_of_lt_of_le hjlt hlen
            calc
              row.entry j < lower.entry j := hpair_tail.1 j hjlt
              _ = (lower ++ [k]).entry j := by
                symm
                exact Row.entry_append_left _ _ hjlt
          ·
            have hshape'' : ShapeSorted (row :: (lower ++ [k]) :: tail) := by
              simpa [recordAt] using hshape'
            have hlen : lower.length + 1 ≤ row.length :=
              by
                have hlen' : (lower ++ [k]).length ≤ row.length :=
                  length_head_le_of_shapeSorted_cons_cons hshape''
                simpa [List.length_append] using hlen'
            have hjrow : lower.length < row.length := by omega
            have hltk : row.entry lower.length < k :=
              entry_lt_of_entriesLt hlt (by simp) hjrow
            have hnew : (lower ++ [k]).entry lower.length = k := by
              calc
                (lower ++ [k]).entry lower.length = Row.entry [k] 0 := by
                  rw [Row.entry_append_right _ _ (Nat.le_refl _)]
                  simp
                _ = k := by simp [Row.entry]
            rwa [hnew]
      | succ i =>
          rw [recordAt]
          have hpair_tail :
              ColumnStrictTwoRows row lower ∧ ColumnStrict (lower :: tail) := by
            simpa using (columnStrict_cons_cons_iff (upper := row) (lower := lower) (rows := tail)).1 hcol
          have hnonempty_tail : RowsNonempty (lower :: tail) := by
            intro r hr
            exact hnonempty r (by simp [hr])
          have hshape_tail : ShapeSorted (lower :: tail) := shapeSorted_tail_of_cons hshape
          have hlt_tail : EntriesLt k (lower :: tail) := by
            intro r hr x hx
            exact hlt r (by simp [hr]) x hx
          have hshape'_tail : ShapeSorted (recordAt k (i + 1) (lower :: tail)) := by
            simpa [recordAt] using shapeSorted_tail_of_cons hshape'
          simpa [recordAt] using
            (columnStrict_cons_cons_iff
              (upper := row) (lower := lower) (rows := recordAt k i tail)).2
              ⟨hpair_tail.1,
                columnStrict_recordAt k (i + 1) (lower :: tail)
                  hnonempty_tail hshape_tail hpair_tail.2 hlt_tail hshape'_tail⟩

theorem isRSTableau_recordAt {k i : ℕ} {rows : List Row}
    (hT : IsRSTableau rows) (hlt : EntriesLt k rows) (hi : i ≤ rows.length)
    (hshape : ShapeSorted (recordAt k i rows)) :
    IsRSTableau (recordAt k i rows) := by
  rcases hT with ⟨hnonempty, hstrict, hshape₀, hcol⟩
  refine ⟨?_, ?_, hshape, ?_⟩
  · exact rowsNonempty_recordAt k i rows hnonempty hi
  · exact rowsStrict_recordAt k i rows hstrict hlt
  · exact columnStrict_recordAt k i rows hnonempty hshape₀ hcol hlt hshape

theorem shape_recordAt (k : ℕ) :
    ∀ i : ℕ, ∀ rows : List Row, (recordAt k i rows).map List.length = bumpAt i (rows.map List.length)
  | 0, [] => by
      simp [recordAt, bumpAt]
  | 0, row :: rows => by
      simp [recordAt, bumpAt]
  | i + 1, [] => by
      simp [recordAt, bumpAt]
  | i + 1, row :: rows => by
      simp [recordAt, bumpAt, shape_recordAt k i rows]

theorem cellCount_recordAt (k : ℕ) :
    ∀ i : ℕ, ∀ rows : List Row, i ≤ rows.length → cellCount (recordAt k i rows) = cellCount rows + 1
  | 0, [], _ => by
      simp [recordAt, cellCount]
  | 0, row :: rows, _ => by
      rw [recordAt, cellCount_cons, cellCount_cons]
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | i + 1, [], hi => by
      cases hi
  | i + 1, row :: rows, hi => by
      have hi' : i ≤ rows.length := Nat.le_of_succ_le_succ hi
      rw [recordAt, cellCount_cons, cellCount_cons, cellCount_recordAt k i rows hi']
      omega

theorem perm_flatten_recordAt (k : ℕ) :
    ∀ i : ℕ, ∀ rows : List Row, i ≤ rows.length →
      List.Perm (recordAt k i rows).flatten (k :: rows.flatten)
  | 0, [], _ => by
      simp [recordAt]
  | 0, row :: rows, _ => by
      simpa [recordAt, List.flatten, List.append_assoc] using
        (List.perm_middle : List.Perm (row ++ k :: rows.flatten) (k :: row ++ rows.flatten))
  | i + 1, [], hi => by
      cases hi
  | i + 1, row :: rows, hi => by
      have hi' : i ≤ rows.length := Nat.le_of_succ_le_succ hi
      have ih := perm_flatten_recordAt k i rows hi'
      have hmid : List.Perm (row ++ k :: rows.flatten) (k :: row ++ rows.flatten) := by
        simpa [List.append_assoc] using
          (List.perm_middle : List.Perm (row ++ k :: rows.flatten) (k :: row ++ rows.flatten))
      exact (by
        simpa [recordAt, List.flatten, List.append_assoc] using (ih.append_left row).trans hmid)

theorem entriesNodup_recordAt {k i : ℕ} {rows : List Row}
    (hnd : EntriesNodup rows) (hlt : EntriesLt k rows) (hi : i ≤ rows.length) :
    EntriesNodup (recordAt k i rows) := by
  rw [EntriesNodup]
  have hkfresh : k ∉ rows.flatten := by
    intro hk
    rcases List.mem_flatten.1 hk with ⟨row, hrow, hkrow⟩
    exact Nat.lt_irrefl _ (hlt row hrow k hkrow)
  exact (perm_flatten_recordAt k i rows hi).nodup_iff.2 (List.nodup_cons.2 ⟨hkfresh, hnd⟩)

theorem shape_insertRows (x : ℕ) :
    ∀ rows : List Row, (insertRows x rows).rows.map List.length = bumpAt (insertRows x rows).newRow
      (rows.map List.length)
  | [] => by
      simp [insertRows, bumpAt]
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
              simp [insertRows, bumpAt, hri, hlen']
          | some y =>
              have hbump : Row.bump? x row = some y := by
                simpa [Row.bumped_insert] using congrArg Row.InsertResult.bumped hri
              have hlen := Row.length_insert_of_bump_some (row := row) (x := x) hbump
              have hlen' : row'.length = row.length := by
                simpa [hri] using hlen
              simpa [insertRows, bumpAt, hri, hlen'] using shape_insertRows y rows

structure State where
  P : List Row
  Q : List Row

/-- Labels `label, label + 1, ..., label + len - 1` listed in reverse order. -/
def revLabelsFrom : ℕ → ℕ → List ℕ
  | _, 0 => []
  | label, len + 1 => revLabelsFrom (label + 1) len ++ [label]

theorem le_of_mem_revLabelsFrom {label len x : ℕ}
    (hx : x ∈ revLabelsFrom label len) :
    label ≤ x := by
  induction len generalizing label with
  | zero =>
      simp [revLabelsFrom] at hx
  | succ len ih =>
      simp [revLabelsFrom, List.mem_append] at hx
      rcases hx with hx | hx
      · exact le_trans (Nat.le_succ _) (ih hx)
      · have hx' : x = label := by simpa using hx
        subst hx'
        omega

theorem lt_add_of_mem_revLabelsFrom {label len x : ℕ}
    (hx : x ∈ revLabelsFrom label len) :
    x < label + len := by
  induction len generalizing label with
  | zero =>
      simp [revLabelsFrom] at hx
  | succ len ih =>
      simp [revLabelsFrom, List.mem_append] at hx
      rcases hx with hx | hx
      · have hlt : x < (label + 1) + len := ih hx
        omega
      · have hx' : x = label := by simpa using hx
        subst hx'
        omega

theorem nodup_revLabelsFrom (label len : ℕ) :
    (revLabelsFrom label len).Nodup := by
  induction len generalizing label with
  | zero =>
      simp [revLabelsFrom]
  | succ len ih =>
      have hnot : label ∉ revLabelsFrom (label + 1) len := by
        intro hmem
        have hle : label + 1 ≤ label := le_of_mem_revLabelsFrom hmem
        omega
      rw [revLabelsFrom]
      refine List.nodup_append'.2 ?_
      refine ⟨ih _, by simp, List.disjoint_right.2 ?_⟩
      intro a ha
      have ha' : a = label := by simpa using ha
      subst ha'
      exact hnot

/-- One forward RS step: insert the next value into `P` and record the created box in `Q`. -/
def step (label x : ℕ) (s : State) : State :=
  let ins := insertRows x s.P
  { P := ins.rows
    Q := recordAt label ins.newRow s.Q }

theorem shape_step {label x : ℕ} {s : State}
    (hshape : s.P.map List.length = s.Q.map List.length) :
    (step label x s).P.map List.length = (step label x s).Q.map List.length := by
  unfold step
  simp [shape_insertRows, shape_recordAt, hshape]

theorem cellCount_step_P {label x : ℕ} {s : State} :
    cellCount (step label x s).P = cellCount s.P + 1 := by
  unfold step
  simp [cellCount_insertRows]

theorem perm_flatten_step_P {label x : ℕ} {s : State} :
    List.Perm (step label x s).P.flatten (x :: s.P.flatten) := by
  unfold step
  simpa [List.flatten] using perm_flatten_insertRows x s.P

theorem cellCount_step_Q {label x : ℕ} {s : State}
    (hshape : s.P.map List.length = s.Q.map List.length) :
    cellCount (step label x s).Q = cellCount s.Q + 1 := by
  unfold step
  let ins := insertRows x s.P
  have hshapeLen : s.P.length = s.Q.length := by
    simpa using congrArg List.length hshape
  have hnewRow : ins.newRow ≤ s.Q.length := by
    rw [← hshapeLen]
    simpa [ins] using newRow_le_length_insertRows x s.P
  simpa [ins] using cellCount_recordAt label ins.newRow s.Q hnewRow

theorem perm_flatten_step_Q {label x : ℕ} {s : State}
    (hshape : s.P.map List.length = s.Q.map List.length) :
    List.Perm (step label x s).Q.flatten (label :: s.Q.flatten) := by
  unfold step
  let ins := insertRows x s.P
  have hshapeLen : s.P.length = s.Q.length := by
    simpa using congrArg List.length hshape
  have hnewRow : ins.newRow ≤ s.Q.length := by
    rw [← hshapeLen]
    simpa [ins] using newRow_le_length_insertRows x s.P
  simpa [ins, List.flatten] using perm_flatten_recordAt label ins.newRow s.Q hnewRow

theorem entriesLt_step_Q {label x : ℕ} {s : State}
    (hlt : EntriesLt label s.Q) :
    EntriesLt (label + 1) (step label x s).Q := by
  unfold step
  exact entriesLt_recordAt label _ _ hlt

theorem rowsStrict_step_Q {label x : ℕ} {s : State}
    (hstrict : RowsStrict s.Q) (hlt : EntriesLt label s.Q) :
    RowsStrict (step label x s).Q := by
  unfold step
  exact rowsStrict_recordAt label _ _ hstrict hlt

/-- Iterate forward RS starting from an arbitrary state and initial recording label. -/
def forwardAux : ℕ → List ℕ → State → State
  | _, [], s => s
  | label, x :: xs, s => forwardAux (label + 1) xs (step label x s)

/-- Forward RS on a word, starting with empty insertion and recording tableaux. -/
def forward (w : List ℕ) : State :=
  forwardAux 1 w ⟨[], []⟩

theorem forwardAux_append (label : ℕ) :
    ∀ w₁ w₂ : List ℕ, ∀ s : State,
      forwardAux label (w₁ ++ w₂) s =
        forwardAux (label + w₁.length) w₂ (forwardAux label w₁ s)
  | [], w₂, s => by
      simp [forwardAux]
  | x :: xs, w₂, s => by
      simpa [forwardAux, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (forwardAux_append (label + 1) xs w₂ (step label x s))

theorem forward_snoc (w : List ℕ) (x : ℕ) :
    forward (w ++ [x]) = step (w.length + 1) x (forward w) := by
  simpa [forward, forwardAux, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (forwardAux_append 1 w [x] ⟨[], []⟩)

theorem shape_forwardAux (label : ℕ) :
    ∀ w : List ℕ, ∀ s : State, s.P.map List.length = s.Q.map List.length →
      (forwardAux label w s).P.map List.length = (forwardAux label w s).Q.map List.length
  | [], s, hshape => by
      simpa [forwardAux] using hshape
  | x :: xs, s, hshape => by
      apply shape_forwardAux (label + 1) xs
      exact shape_step (label := label) (x := x) hshape

theorem shape_forward (w : List ℕ) :
    (forward w).P.map List.length = (forward w).Q.map List.length := by
  simpa [forward] using shape_forwardAux 1 w ⟨[], []⟩ rfl

theorem cellCount_forwardAux_P (label : ℕ) :
    ∀ w : List ℕ, ∀ s : State, cellCount (forwardAux label w s).P = cellCount s.P + w.length
  | [], s => by
      simp [forwardAux]
  | x :: xs, s => by
      rw [forwardAux]
      rw [cellCount_forwardAux_P (label + 1) xs (step label x s)]
      rw [cellCount_step_P]
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem cellCount_forwardAux_Q (label : ℕ) :
    ∀ w : List ℕ, ∀ s : State, s.P.map List.length = s.Q.map List.length →
      cellCount (forwardAux label w s).Q = cellCount s.Q + w.length
  | [], s, _ => by
      simp [forwardAux]
  | x :: xs, s, hshape => by
      rw [forwardAux]
      have hstepShape : (step label x s).P.map List.length = (step label x s).Q.map List.length :=
        shape_step (label := label) (x := x) hshape
      rw [cellCount_forwardAux_Q (label + 1) xs (step label x s) hstepShape]
      rw [cellCount_step_Q hshape]
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem cellCount_forward_P (w : List ℕ) :
    cellCount (forward w).P = w.length := by
  simpa [forward] using cellCount_forwardAux_P 1 w ⟨[], []⟩

theorem cellCount_forward_Q (w : List ℕ) :
    cellCount (forward w).Q = w.length := by
  simpa [forward] using cellCount_forwardAux_Q 1 w ⟨[], []⟩ rfl

theorem perm_flatten_forwardAux_P (label : ℕ) :
    ∀ w : List ℕ, ∀ s : State,
      List.Perm (forwardAux label w s).P.flatten (w.reverse ++ s.P.flatten)
  | [], s => by
      simp [forwardAux]
  | x :: xs, s => by
      rw [forwardAux]
      have ih := perm_flatten_forwardAux_P (label + 1) xs (step label x s)
      have hstep := perm_flatten_step_P (label := label) (x := x) (s := s)
      exact ih.trans <| by
        simpa [List.reverse_cons, List.append_assoc] using hstep.append_left xs.reverse

theorem perm_flatten_forward_P (w : List ℕ) :
    List.Perm (forward w).P.flatten w.reverse := by
  simpa [forward] using perm_flatten_forwardAux_P 1 w ⟨[], []⟩

theorem perm_flatten_forwardAux_Q (label : ℕ) :
    ∀ w : List ℕ, ∀ s : State,
      s.P.map List.length = s.Q.map List.length →
      List.Perm (forwardAux label w s).Q.flatten (revLabelsFrom label w.length ++ s.Q.flatten)
  | [], s, _ => by
      simp [forwardAux, revLabelsFrom]
  | x :: xs, s, hshape => by
      rw [forwardAux]
      have hstepShape : (step label x s).P.map List.length = (step label x s).Q.map List.length :=
        shape_step (label := label) (x := x) hshape
      have ih := perm_flatten_forwardAux_Q (label + 1) xs (step label x s) hstepShape
      have hstep := perm_flatten_step_Q (label := label) (x := x) hshape
      exact ih.trans <| by
        simpa [revLabelsFrom, List.append_assoc] using
          hstep.append_left (revLabelsFrom (label + 1) xs.length)

theorem perm_flatten_forward_Q (w : List ℕ) :
    List.Perm (forward w).Q.flatten (revLabelsFrom 1 w.length) := by
  simpa [forward] using perm_flatten_forwardAux_Q 1 w ⟨[], []⟩ rfl

theorem entriesNodup_forward_P {w : List ℕ} (hnd : w.Nodup) :
    EntriesNodup (forward w).P := by
  rw [EntriesNodup]
  have hrev : w.reverse.Nodup := (List.nodup_reverse).2 hnd
  exact (perm_flatten_forward_P w).nodup_iff.2 hrev

theorem rowsNonempty_forwardAux_P (label : ℕ) :
    ∀ w : List ℕ, ∀ s : State, RowsNonempty s.P →
      RowsNonempty (forwardAux label w s).P
  | [], s, hnonempty => by
      simpa [forwardAux] using hnonempty
  | x :: xs, s, hnonempty => by
      have hstepNonempty : RowsNonempty (step label x s).P := by
        unfold step
        intro row hrow
        exact rows_nonempty_insertRows x hnonempty row hrow
      simpa [forwardAux] using
        rowsNonempty_forwardAux_P (label + 1) xs (step label x s) hstepNonempty

theorem rowsNonempty_forward_P (w : List ℕ) :
    RowsNonempty (forward w).P := by
  apply rowsNonempty_forwardAux_P 1 w ⟨[], []⟩
  intro row hrow
  simp at hrow

theorem isRSTableau_entriesNodup_forwardAux_P (label : ℕ) :
    ∀ w : List ℕ, ∀ s : State,
      IsRSTableau s.P → EntriesNodup s.P → List.Disjoint w s.P.flatten → w.Nodup →
      IsRSTableau (forwardAux label w s).P ∧ EntriesNodup (forwardAux label w s).P
  | [], s, hT, hnd, _, _ => by
      simpa [forwardAux] using And.intro hT hnd
  | x :: xs, s, hT, hnd, hdisj, hnodup => by
      have hcons := List.nodup_cons.1 hnodup
      have hdisj₀ : x ∉ s.P.flatten := by
        intro hxp
        exact (List.disjoint_left.1 hdisj) (by simp) hxp
      have hstepT : IsRSTableau (step label x s).P := by
        unfold step
        exact isRSTableau_insertRows hT hnd hdisj₀
      have hstepNodup : EntriesNodup (step label x s).P := by
        unfold step
        exact entriesNodup_insertRows hnd hdisj₀
      have hdisj₁ : List.Disjoint xs (x :: s.P.flatten) := by
        refine List.disjoint_right.2 ?_
        intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hcons.1
        ·
          intro hax
          exact (List.disjoint_right.1 hdisj) ha (by simp [hax])
      have hstepDisj : List.Disjoint xs (step label x s).P.flatten := by
        exact (perm_flatten_step_P (label := label) (x := x) (s := s)).disjoint_right.2 hdisj₁
      exact isRSTableau_entriesNodup_forwardAux_P (label + 1) xs (step label x s)
        hstepT hstepNodup hstepDisj hcons.2

theorem isRSTableau_forward_P {w : List ℕ} (hnd : w.Nodup) :
    IsRSTableau (forward w).P := by
  exact (isRSTableau_entriesNodup_forwardAux_P 1 w ⟨[], []⟩
    (by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro row hrow
        simp at hrow
      · intro row hrow
        simp at hrow
      · exact shapeSorted_nil
      · exact columnStrict_nil)
    (by simp [EntriesNodup])
    (by simp)
    hnd).1

theorem rowsStrict_entriesNodup_forwardAux_P (label : ℕ) :
    ∀ w : List ℕ, ∀ s : State,
      RowsStrict s.P → EntriesNodup s.P → List.Disjoint w s.P.flatten → w.Nodup →
      RowsStrict (forwardAux label w s).P ∧ EntriesNodup (forwardAux label w s).P
  | [], s, hstrict, hnd, _, _ => by
      simpa [forwardAux] using And.intro hstrict hnd
  | x :: xs, s, hstrict, hnd, hdisj, hnodup => by
      have hcons := List.nodup_cons.1 hnodup
      have hxfresh : x ∉ s.P.flatten := by
        exact (List.disjoint_left.1 hdisj) (by simp)
      have hstepStrict : RowsStrict (step label x s).P := by
        unfold step
        exact rowsStrict_insertRows hstrict hnd hxfresh
      have hstepNodup : EntriesNodup (step label x s).P := by
        unfold step
        exact entriesNodup_insertRows hnd hxfresh
      have hdisj₀ : List.Disjoint xs (x :: s.P.flatten) := by
        refine List.disjoint_right.2 ?_
        intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hcons.1
        ·
          intro hax
          exact (List.disjoint_right.1 hdisj) ha (by simp [hax])
      have hdisj_step : List.Disjoint xs (step label x s).P.flatten := by
        exact (perm_flatten_step_P (label := label) (x := x) (s := s)).disjoint_right.2 hdisj₀
      exact rowsStrict_entriesNodup_forwardAux_P (label + 1) xs (step label x s)
        hstepStrict hstepNodup hdisj_step hcons.2

theorem rowsStrict_forward_P {w : List ℕ} (hnd : w.Nodup) :
    RowsStrict (forward w).P := by
  exact (rowsStrict_entriesNodup_forwardAux_P 1 w ⟨[], []⟩
    (by intro row hrow; simp at hrow)
    (by simp [EntriesNodup])
    (by simp)
    hnd).1

theorem entriesLt_forwardAux_Q (label : ℕ) :
    ∀ w : List ℕ, ∀ s : State, EntriesLt label s.Q →
      EntriesLt (label + w.length) (forwardAux label w s).Q
  | [], s, hlt => by
      simpa [forwardAux] using hlt
  | x :: xs, s, hlt => by
      have hstepLt : EntriesLt (label + 1) (step label x s).Q :=
        entriesLt_step_Q (label := label) (x := x) hlt
      simpa [forwardAux, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        entriesLt_forwardAux_Q (label + 1) xs (step label x s) hstepLt

theorem rowsStrict_forwardAux_Q (label : ℕ) :
    ∀ w : List ℕ, ∀ s : State, RowsStrict s.Q → EntriesLt label s.Q →
      RowsStrict (forwardAux label w s).Q
  | [], s, hstrict, _ => by
      simpa [forwardAux] using hstrict
  | x :: xs, s, hstrict, hlt => by
      have hstepStrict : RowsStrict (step label x s).Q :=
        rowsStrict_step_Q (label := label) (x := x) hstrict hlt
      have hstepLt : EntriesLt (label + 1) (step label x s).Q :=
        entriesLt_step_Q (label := label) (x := x) hlt
      simpa [forwardAux] using
        rowsStrict_forwardAux_Q (label + 1) xs (step label x s) hstepStrict hstepLt

theorem rowsStrict_forward_Q (w : List ℕ) :
    RowsStrict (forward w).Q := by
  apply rowsStrict_forwardAux_Q 1 w ⟨[], []⟩
  · intro row hrow
    simp at hrow
  · intro row hrow
    simp at hrow

theorem shapeSorted_forward_Q {w : List ℕ} (hnd : w.Nodup) :
    ShapeSorted (forward w).Q := by
  simpa [ShapeSorted, shape_forward w] using (isRSTableau_forward_P hnd).2.2.1

theorem rowsNonempty_forwardAux_Q (label : ℕ) :
    ∀ w : List ℕ, ∀ s : State, RowsNonempty s.Q →
      s.P.map List.length = s.Q.map List.length →
      RowsNonempty (forwardAux label w s).Q
  | [], s, hnonempty, _ => by
      simpa [forwardAux] using hnonempty
  | x :: xs, s, hnonempty, hshape => by
      have hstepShape : (step label x s).P.map List.length = (step label x s).Q.map List.length :=
        shape_step (label := label) (x := x) hshape
      have hnewRow : (insertRows x s.P).newRow ≤ s.Q.length := by
        have hshapeLen : s.P.length = s.Q.length := by
          simpa using congrArg List.length hshape
        rw [← hshapeLen]
        simpa using newRow_le_length_insertRows x s.P
      have hstepNonempty : RowsNonempty (step label x s).Q := by
        unfold step
        exact rowsNonempty_recordAt label _ _ hnonempty hnewRow
      simpa [forwardAux] using
        rowsNonempty_forwardAux_Q (label + 1) xs (step label x s) hstepNonempty hstepShape

theorem rowsNonempty_forward_Q (w : List ℕ) :
    RowsNonempty (forward w).Q := by
  apply rowsNonempty_forwardAux_Q 1 w ⟨[], []⟩
  · intro row hrow
    simp at hrow
  · rfl

theorem entriesNodup_forwardAux_Q (label : ℕ) :
    ∀ w : List ℕ, ∀ s : State,
      s.P.map List.length = s.Q.map List.length →
      EntriesNodup s.Q → EntriesLt label s.Q →
      EntriesNodup (forwardAux label w s).Q
  | [], s, _, hnd, _ => by
      simpa [forwardAux] using hnd
  | x :: xs, s, hshape, hnd, hlt => by
      have hnewRow : (insertRows x s.P).newRow ≤ s.Q.length := by
        have hshapeLen : s.P.length = s.Q.length := by
          simpa using congrArg List.length hshape
        rw [← hshapeLen]
        simpa using newRow_le_length_insertRows x s.P
      have hstepShape : (step label x s).P.map List.length = (step label x s).Q.map List.length :=
        shape_step (label := label) (x := x) hshape
      have hstepNodup : EntriesNodup (step label x s).Q := by
        unfold step
        exact entriesNodup_recordAt hnd hlt hnewRow
      have hstepLt : EntriesLt (label + 1) (step label x s).Q :=
        entriesLt_step_Q (label := label) (x := x) hlt
      simpa [forwardAux] using
        entriesNodup_forwardAux_Q (label + 1) xs (step label x s) hstepShape hstepNodup hstepLt

theorem entriesNodup_forward_Q (w : List ℕ) :
    EntriesNodup (forward w).Q := by
  apply entriesNodup_forwardAux_Q 1 w ⟨[], []⟩
  · rfl
  · simp [EntriesNodup]
  · intro row hrow
    simp at hrow

theorem entriesLt_forward_Q (w : List ℕ) :
    EntriesLt (w.length + 1) (forward w).Q := by
  simpa [forward, Nat.add_comm] using entriesLt_forwardAux_Q 1 w ⟨[], []⟩ (by
    intro row hrow
    simp at hrow)

theorem isRSTableau_forward_Q {w : List ℕ} (hnd : w.Nodup) :
    IsRSTableau (forward w).Q := by
  induction w using List.reverseRecOn with
  | nil =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro row hrow
        cases hrow
      · intro row hrow
        cases hrow
      · exact shapeSorted_nil
      · exact columnStrict_nil
  | append_singleton w x ih =>
      have hwnd : w.Nodup := (List.nodup_append.1 hnd).1
      rw [forward_snoc]
      let ins := insertRows x (forward w).P
      have hshapeLen : (forward w).P.length = (forward w).Q.length := by
        simpa using congrArg List.length (shape_forward w)
      have hnewRow : ins.newRow ≤ (forward w).Q.length := by
        rw [← hshapeLen]
        simpa [ins] using newRow_le_length_insertRows x (forward w).P
      have hshape : ShapeSorted (recordAt (w.length + 1) ins.newRow (forward w).Q) := by
        simpa [forward_snoc, step, ins] using shapeSorted_forward_Q hnd
      unfold step
      exact isRSTableau_recordAt (ih hwnd) (entriesLt_forward_Q w) hnewRow hshape

/-- Forward Robinson-Schensted on a permutation of `1, …, n` produces a pair of RS tableaux of the
same shape whose entries are exactly `1, …, n`. -/
theorem forward_perm_rs_spec {w : List ℕ}
    (hw : List.Perm w (revLabelsFrom 1 w.length)) :
    let s := forward w
    IsRSTableau s.P ∧
    EntriesNodup s.P ∧
    IsRSTableau s.Q ∧
    EntriesNodup s.Q ∧
    s.P.map List.length = s.Q.map List.length ∧
    List.Perm s.P.flatten (revLabelsFrom 1 w.length) ∧
    List.Perm s.Q.flatten (revLabelsFrom 1 w.length) := by
  have hnd : w.Nodup := (hw.nodup_iff).2 (nodup_revLabelsFrom 1 w.length)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isRSTableau_forward_P hnd
  · exact entriesNodup_forward_P hnd
  · exact isRSTableau_forward_Q hnd
  · exact entriesNodup_forward_Q w
  · exact shape_forward w
  · exact (perm_flatten_forward_P w).trans (w.reverse_perm.trans hw)
  · exact perm_flatten_forward_Q w

/-- Forward Robinson-Schensted on a word with distinct letters produces:
- a row-strict insertion tableau `P`,
- a row-strict recording tableau `Q`,
- no repeated entries in either tableau,
- the same shape for `P` and `Q`,
- and the expected flattened contents.

This packages the theorem-level guarantees already proved throughout the development into a single
statement about the forward algorithm. -/
theorem forward_nodup_spec {w : List ℕ} (hnd : w.Nodup) :
    let s := forward w
    RowsStrict s.P ∧
    EntriesNodup s.P ∧
    RowsStrict s.Q ∧
    EntriesNodup s.Q ∧
    EntriesLt (w.length + 1) s.Q ∧
    s.P.map List.length = s.Q.map List.length ∧
    cellCount s.P = w.length ∧
    cellCount s.Q = w.length ∧
    List.Perm s.P.flatten w.reverse ∧
    List.Perm s.Q.flatten (revLabelsFrom 1 w.length) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact rowsStrict_forward_P hnd
  · exact entriesNodup_forward_P hnd
  · exact rowsStrict_forward_Q w
  · exact entriesNodup_forward_Q w
  · exact entriesLt_forward_Q w
  · exact shape_forward w
  · exact cellCount_forward_P w
  · exact cellCount_forward_Q w
  · exact perm_flatten_forward_P w
  · exact perm_flatten_forward_Q w

/-- If the input word is a permutation of the labels `1, …, n` encoded as
`revLabelsFrom 1 n`, then both forward tableaux have that same label multiset. -/
theorem forward_perm_flatten_spec {w : List ℕ}
    (hw : List.Perm w (revLabelsFrom 1 w.length)) :
    let s := forward w
    List.Perm s.P.flatten (revLabelsFrom 1 w.length) ∧
    List.Perm s.Q.flatten (revLabelsFrom 1 w.length) := by
  refine ⟨?_, ?_⟩
  · exact (perm_flatten_forward_P w).trans (w.reverse_perm.trans hw)
  · exact perm_flatten_forward_Q w

end RS
