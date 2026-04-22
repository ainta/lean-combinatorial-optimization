import RS.Tableau
import Mathlib.Data.List.Sort
import Batteries.Data.List.Lemmas

/-!
# Row insertion

This file implements one-row insertion for the Robinson-Schensted correspondence. Since the
current scope is permutations, rows are treated as strictly increasing lists.
-/

namespace RS

namespace Row

/-- Rows used in the RS correspondence are strictly increasing. -/
def Strict (row : Row) : Prop :=
  row.SortedLT

/-- The first element of `row` that is strictly greater than `x`, if it exists. -/
def bump? (x : ℕ) (row : Row) : Option ℕ :=
  row.find? (fun y => x ≤ y)

/-- The auxiliary list obtained by inserting `x` into the strict row in sorted order. -/
def inserted (x : ℕ) (row : Row) : Row :=
  row.orderedInsert (· ≤ ·) x

structure InsertResult where
  row : Row
  bumped : Option ℕ

/-- One-row insertion for strict rows: insert `x`, and if a larger entry is displaced, return it
as `bumped`. -/
def insert (x : ℕ) (row : Row) : InsertResult :=
  match h : bump? x row with
  | none => ⟨inserted x row, none⟩
  | some y => ⟨(inserted x row).erase y, some y⟩

@[simp]
theorem bumped_insert (x : ℕ) (row : Row) : (insert x row).bumped = bump? x row := by
  unfold insert
  split <;> simp_all

theorem mem_of_bump?_eq_some {x y : ℕ} {row : Row} (h : bump? x row = some y) : y ∈ row :=
  List.mem_of_find?_eq_some h

theorem le_of_bump?_eq_some {x y : ℕ} {row : Row} (h : bump? x row = some y) : x ≤ y := by
  simpa [bump?] using List.find?_some h

theorem bump?_eq_some_iff_append {x y : ℕ} {row : Row} :
    bump? x row = some y ↔
      x ≤ y ∧ ∃ as bs, row = as ++ y :: bs ∧ ∀ a ∈ as, ¬ x ≤ a := by
  simpa [bump?, and_left_comm, and_assoc] using
    (List.find?_eq_some_iff_append (xs := row) (p := fun z => x ≤ z) (b := y))

theorem bump?_spec {x y : ℕ} {row : Row} (h : bump? x row = some y) :
    ∃ as bs, row = as ++ y :: bs ∧ (∀ a ∈ as, ¬ x ≤ a) ∧ x ≤ y := by
  rcases (bump?_eq_some_iff_append.1 h) with ⟨hxy, as, bs, hr, hprefix⟩
  exact ⟨as, bs, hr, hprefix, hxy⟩

theorem bump?_prefix_lt {x y : ℕ} {row : Row} (h : bump? x row = some y) :
    ∃ as bs, row = as ++ y :: bs ∧ (∀ a ∈ as, a < x) ∧ x ≤ y := by
  rcases bump?_spec h with ⟨as, bs, hr, hprefix, hxy⟩
  refine ⟨as, bs, hr, ?_, hxy⟩
  intro a ha
  exact Nat.lt_of_not_ge (hprefix a ha)

theorem inserted_eq_append_of_prefix_lt {x y : ℕ} {as bs : Row}
    (hprefix : ∀ a ∈ as, a < x) (hxy : x ≤ y) :
    inserted x (as ++ y :: bs) = as ++ x :: y :: bs := by
  induction as with
  | nil =>
      simpa [inserted] using
        (List.orderedInsert_cons_of_le (r := (· ≤ ·)) (a := x) (b := y) (l := bs) hxy)
  | cons a as ih =>
      have hax : ¬ x ≤ a := Nat.not_le_of_lt (hprefix a (by simp))
      have hprefix' : ∀ b ∈ as, b < x := by
        intro b hb
        exact hprefix b (by simp [hb])
      change List.orderedInsert (fun x1 x2 => x1 ≤ x2) x (a :: (as ++ y :: bs)) =
          a :: (as ++ x :: y :: bs)
      rw [List.orderedInsert_cons, if_neg hax]
      simpa [inserted, List.append_assoc] using congrArg (List.cons a) (ih hprefix')

theorem not_lt_of_bump?_eq_none {x y : ℕ} {row : Row} (h : bump? x row = none) (hy : y ∈ row) :
    ¬ x ≤ y := by
  simpa [bump?] using List.find?_eq_none.1 h y hy

theorem exists_bump?_of_lt_entry {x : ℕ} {row : Row} {j : ℕ}
    (hj : j < row.length) (hxj : x < row.entry j) :
    ∃ y, bump? x row = some y := by
  cases hb : bump? x row with
  | none =>
      have hmem : row.entry j ∈ row := by
        rw [Row.entry_eq_getElem row hj]
        exact List.getElem_mem hj
      exact False.elim <| (not_lt_of_bump?_eq_none hb hmem) (Nat.le_of_lt hxj)
  | some y =>
      exact ⟨y, by simpa using hb⟩

theorem lt_bumped_of_bump {x y : ℕ} {row : Row} (hx : x ∉ row) (h : bump? x row = some y) :
    x < y := by
  refine lt_of_le_of_ne (le_of_bump?_eq_some h) ?_
  intro hxy
  exact hx (hxy ▸ mem_of_bump?_eq_some h)

theorem inserted_eq_append_of_bump_none {x : ℕ} :
    ∀ {row : Row}, bump? x row = none → inserted x row = row ++ [x]
  | [], _ => by
      simp [inserted]
  | a :: row, h => by
      have hxa : ¬ x ≤ a := not_lt_of_bump?_eq_none h (by simp)
      have htail : bump? x row = none := by
        simpa [bump?, hxa] using h
      rw [inserted, List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := row) hxa]
      simpa [List.append_assoc] using
        congrArg (List.cons a) (inserted_eq_append_of_bump_none (row := row) htail)

theorem strict_inserted {x : ℕ} {row : Row} (hrow : row.Strict) (hx : x ∉ row) :
    (inserted x row).Strict := by
  have hsorted : (inserted x row).SortedLE := by
    exact (hrow.sortedLE.pairwise.orderedInsert x row).sortedLE
  have hnodup : (inserted x row).Nodup := by
    exact (List.perm_orderedInsert (r := (· ≤ ·)) x row).nodup_iff.2
      (List.nodup_cons.2 ⟨hx, hrow.nodup⟩)
  exact hsorted.sortedLT_of_nodup hnodup

theorem strict_insert {x : ℕ} {row : Row} (hrow : row.Strict) (hx : x ∉ row) :
    (insert x row).row.Strict := by
  unfold insert
  split
  · simpa [inserted] using strict_inserted (x := x) hrow hx
  ·
    have hp : (inserted x row).Pairwise (· < ·) := (strict_inserted (x := x) hrow hx).pairwise
    exact (hp.sublist List.erase_sublist).sortedLT

theorem length_insert_of_bump_none {x : ℕ} {row : Row} (h : bump? x row = none) :
    (insert x row).row.length = row.length + 1 := by
  unfold insert
  rw [h]
  simp [inserted, List.orderedInsert_length]

theorem length_insert_of_bump_some {x y : ℕ} {row : Row} (h : bump? x row = some y) :
    (insert x row).row.length = row.length := by
  have hy_row : y ∈ row := mem_of_bump?_eq_some h
  have hy_inserted : y ∈ inserted x row := by
    simpa [inserted, List.mem_orderedInsert] using Or.inr hy_row
  have hlen_erase := List.length_erase_add_one (l := inserted x row) (a := y) hy_inserted
  have hlen_inserted := List.orderedInsert_length (r := (· ≤ ·)) row x
  unfold insert
  rw [h]
  exact Nat.succ.inj (hlen_erase.trans hlen_inserted)

theorem length_pos_insert (x : ℕ) (row : Row) : 0 < (insert x row).row.length := by
  cases h : bump? x row with
  | none =>
      unfold insert
      rw [h]
      simp [inserted, List.orderedInsert_length]
  | some y =>
      have hlen := length_insert_of_bump_some (row := row) (x := x) h
      have hrow : 0 < row.length := by
        cases row with
        | nil => simp [bump?] at h
        | cons a tail => simp
      have hlen' : (List.erase (inserted x row) y).length = row.length := by
        unfold insert at hlen
        rw [h] at hlen
        exact hlen
      unfold insert
      rw [h, hlen']
      exact hrow

theorem self_mem_insert {x : ℕ} {row : Row} (hx : x ∉ row) : x ∈ (insert x row).row := by
  unfold insert
  cases h : bump? x row with
  | none =>
      simpa [h, inserted, List.mem_orderedInsert]
  | some y =>
      have hx_inserted : x ∈ inserted x row := by
        simpa [inserted, List.mem_orderedInsert]
      have hy_row : y ∈ row := mem_of_bump?_eq_some h
      have hxy : x ≠ y := by
        exact fun hxy => hx (hxy ▸ hy_row)
      simpa [h] using (List.mem_erase_of_ne hxy).2 hx_inserted

theorem mem_insert_or_bumped_iff {x z : ℕ} {row : Row} :
    z ∈ (insert x row).row ∨ (insert x row).bumped = some z ↔ z = x ∨ z ∈ row := by
  unfold insert
  cases h : bump? x row with
  | none =>
      simp [h, inserted, List.mem_orderedInsert]
  | some y =>
      have hy_row : y ∈ row := mem_of_bump?_eq_some h
      have hy_inserted : y ∈ inserted x row := by
        simpa [inserted, List.mem_orderedInsert] using Or.inr hy_row
      constructor
      · intro hz
        rcases hz with hz | hz
        · have hz' : z ∈ inserted x row := List.mem_of_mem_erase hz
          simpa [inserted, List.mem_orderedInsert] using hz'
        · right
          have hyz : y = z := by
            simpa [h] using hz
          exact hyz ▸ hy_row
      · intro hz
        rcases hz with hzx | hz
        · by_cases hxy : y = x
          · right
            subst hxy
            subst hzx
            simp [h]
          · left
            have hx_inserted : x ∈ inserted x row := by
              simpa [inserted, List.mem_orderedInsert]
            have hxy' : x ≠ y := by
              intro hxy'
              exact hxy hxy'.symm
            simpa [hzx, h] using (List.mem_erase_of_ne hxy').2 hx_inserted
        · by_cases hzy : z = y
          · right
            simpa [hzy, h]
          · left
            have hz_inserted : z ∈ inserted x row := by
              simpa [inserted, List.mem_orderedInsert] using Or.inr hz
            simpa [h] using (List.mem_erase_of_ne hzy).2 hz_inserted

theorem perm_insert_bumped (x : ℕ) (row : Row) :
    List.Perm ((insert x row).row ++ (insert x row).bumped.toList) (x :: row) := by
  unfold insert
  cases h : bump? x row with
  | none =>
      simpa [h, inserted] using (List.perm_orderedInsert (r := (· ≤ ·)) x row)
  | some y =>
      have hy_row : y ∈ row := mem_of_bump?_eq_some h
      have hy_inserted : y ∈ inserted x row := by
        simpa [inserted, List.mem_orderedInsert] using Or.inr hy_row
      have hperm₁ : List.Perm ((List.erase (inserted x row) y) ++ [y]) (y :: List.erase (inserted x row) y) := by
        simpa using (List.perm_middle :
          List.Perm (List.erase (inserted x row) y ++ y :: []) (y :: (List.erase (inserted x row) y ++ [])))
      have hperm₂ : List.Perm (y :: List.erase (inserted x row) y) (inserted x row) :=
        (List.perm_cons_erase hy_inserted).symm
      have hperm₃ : List.Perm (inserted x row) (x :: row) := by
        simpa [inserted] using (List.perm_orderedInsert (r := (· ≤ ·)) x row)
      exact hperm₁.trans (hperm₂.trans hperm₃)

theorem insert_eq_append_of_bump {x y : ℕ} {row : Row}
    (hrow : row.Strict) (hx : x ∉ row) (h : bump? x row = some y) :
    ∃ as bs, row = as ++ y :: bs ∧
      (insert x row).row = as ++ x :: bs ∧
      (∀ a ∈ as, a < x) ∧ x < y := by
  rcases bump?_prefix_lt h with ⟨as, bs, hr, hprefix, hxy_le⟩
  have hxy : x < y := lt_bumped_of_bump hx h
  have hins : inserted x row = as ++ x :: y :: bs := by
    rw [hr, inserted_eq_append_of_prefix_lt hprefix hxy_le]
  have hnodup : (as ++ y :: bs).Nodup := by
    simpa [hr] using hrow.nodup
  have hy_notin_as : y ∉ as := by
    intro hy
    exact (Nat.lt_asymm (hprefix y hy) hxy).elim
  have hy_notin_bs : y ∉ bs := by
    have htail : (y :: bs).Nodup := (List.nodup_append.1 hnodup).2.1
    simpa using (List.nodup_cons.1 htail).1
  refine ⟨as, bs, hr, ?_, hprefix, hxy⟩
  unfold insert
  rw [h, hins]
  calc
    (as ++ x :: y :: bs).erase y = as ++ (x :: y :: bs).erase y := by
      rw [List.erase_append_right _ hy_notin_as]
    _ = as ++ x :: bs := by
      simp [hxy.ne]

theorem insert_eq_append_of_bump_none {x : ℕ} {row : Row}
    (h : bump? x row = none) :
    (insert x row).row = row ++ [x] := by
  unfold insert
  rw [h]
  simpa [inserted] using inserted_eq_append_of_bump_none (x := x) h

theorem insert_entries_of_bump {x y : ℕ} {row : Row}
    (hrow : row.Strict) (hx : x ∉ row) (h : bump? x row = some y) :
    ∃ as bs, row = as ++ y :: bs ∧
      (insert x row).row = as ++ x :: bs ∧
      (∀ j, j < as.length → (insert x row).row.entry j = row.entry j) ∧
      (insert x row).row.entry as.length = x ∧
      (row.entry as.length = y) ∧
      (∀ k, (insert x row).row.entry (as.length + 1 + k) = row.entry (as.length + 1 + k)) ∧
      x < y := by
  rcases insert_eq_append_of_bump hrow hx h with ⟨as, bs, hr, hins, hprefix, hxy⟩
  refine ⟨as, bs, hr, hins, ?_, ?_, ?_, ?_, hxy⟩
  · intro j hj
    rw [hins, hr]
    calc
      (as ++ x :: bs).entry j = as.entry j := Row.entry_append_left _ _ hj
      _ = (as ++ y :: bs).entry j := by
        symm
        exact Row.entry_append_left _ _ hj
  · rw [hins]
    calc
      (as ++ x :: bs).entry as.length = Row.entry (x :: bs) 0 := by
        rw [Row.entry_append_right _ _ (Nat.le_refl _)]
        simp
      _ = x := by simp [Row.entry]
  · rw [hr]
    calc
      (as ++ y :: bs).entry as.length = Row.entry (y :: bs) 0 := by
        rw [Row.entry_append_right _ _ (Nat.le_refl _)]
        simp
      _ = y := by simp [Row.entry]
  · intro k
    rw [hins, hr]
    calc
      (as ++ x :: bs).entry (as.length + 1 + k) = Row.entry bs k := by
        rw [Row.entry_append_right _ _ (by omega)]
        have hk : as.length + 1 + k - as.length = k + 1 := by omega
        rw [hk]
        simp [Row.entry]
      _ = (as ++ y :: bs).entry (as.length + 1 + k) := by
        symm
        rw [Row.entry_append_right _ _ (by omega)]
        have hk : as.length + 1 + k - as.length = k + 1 := by omega
        rw [hk]
        simp [Row.entry]

theorem insert_entries_of_bump_none {x : ℕ} {row : Row}
    (h : bump? x row = none) :
    (insert x row).row = row ++ [x] ∧
      (∀ j, j < row.length → (insert x row).row.entry j = row.entry j) := by
  refine ⟨insert_eq_append_of_bump_none h, ?_⟩
  intro j hj
  rw [insert_eq_append_of_bump_none h]
  exact Row.entry_append_left _ _ hj

end Row

end RS
