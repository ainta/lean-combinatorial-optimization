import RS.Correspondence

/-!
# Reverse helpers for Robinson-Schensted

This file begins the inverse-direction API from the recording tableau side. The first step is to
remove the most recently recorded label from the row where it was appended.
-/

namespace RS

namespace Row

/-- Remove the last entry of a row, returning that entry together with the remaining prefix. -/
def popLast? : Row → Option (ℕ × Row)
  | [] => none
  | [x] => some (x, [])
  | x :: y :: row =>
      match popLast? (y :: row) with
      | none => none
      | some (z, row') => some (z, x :: row')

theorem popLast?_append_singleton :
    ∀ (row : Row) (x : ℕ), popLast? (row ++ [x]) = some (x, row)
  | [], x => by
      simp [popLast?]
  | [a], x => by
      simp [popLast?]
  | a :: b :: row, x => by
      have htail : popLast? ((b :: row) ++ [x]) = some (x, b :: row) :=
        popLast?_append_singleton (b :: row) x
      simpa [popLast?] using
        congrArg
          (fun t =>
            match t with
            | none => none
            | some (z, row') => some (z, a :: row')) htail
termination_by row => row.length

theorem popLast?_some_of_ne_nil :
    ∀ {row : Row}, row ≠ [] → ∃ x row', popLast? row = some (x, row')
  | [], h => by
      exact False.elim (h rfl)
  | [x], _ => by
      exact ⟨x, [], by simp [popLast?]⟩
  | x :: y :: row, _ => by
      rcases popLast?_some_of_ne_nil (row := y :: row) (by simp) with ⟨z, row', hpop⟩
      exact ⟨z, x :: row', by simp [popLast?, hpop]⟩

theorem popLast?_mem_of_eq_some :
    ∀ {row : Row} {x : ℕ} {row' : Row},
      popLast? row = some (x, row') → x ∈ row
  | [], _, _, h => by
      simp [popLast?] at h
  | [y], x, row', h => by
      simp [popLast?] at h
      rcases h with ⟨rfl, rfl⟩
      simp
  | y :: z :: row, x, row', h => by
      cases htail : popLast? (z :: row) with
      | none =>
          simp [popLast?, htail] at h
      | some p =>
          rcases p with ⟨x', row''⟩
          simp [popLast?, htail] at h
          rcases h with ⟨rfl, rfl⟩
          exact List.mem_cons_of_mem _ (popLast?_mem_of_eq_some htail)

theorem eq_append_singleton_of_popLast?_eq_some :
    ∀ {row : Row} {x : ℕ} {row' : Row},
      popLast? row = some (x, row') → row = row' ++ [x]
  | [], _, _, h => by
      simp [popLast?] at h
  | [y], x, row', h => by
      simp [popLast?] at h
      rcases h with ⟨rfl, rfl⟩
      simp
  | y :: z :: row, x, row', h => by
      cases htail : popLast? (z :: row) with
      | none =>
          simp [popLast?, htail] at h
      | some p =>
          rcases p with ⟨x', row''⟩
          simp [popLast?, htail] at h
          rcases h with ⟨rfl, rfl⟩
          simpa [List.cons_append] using
            congrArg (List.cons y) (eq_append_singleton_of_popLast?_eq_some htail)

theorem lt_last_of_mem_strict_append_singleton :
    ∀ {pre : Row} {x y : ℕ}, Row.Strict (pre ++ [x]) → y ∈ pre → y < x
  | [], _, _, _, hy => by
      cases hy
  | a :: pre, x, y, hstrict, hy => by
      have hpair : List.Pairwise (· < ·) (a :: (pre ++ [x])) := by
        simpa [Row.Strict, List.sortedLT_iff_pairwise, List.cons_append] using hstrict
      have hax : a < x := (List.pairwise_cons.1 hpair).1 _ (by simp)
      have htail : Row.Strict (pre ++ [x]) := by
        simpa [Row.Strict, List.sortedLT_iff_pairwise, List.cons_append] using
          (List.pairwise_cons.1 hpair).2
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hax
      · exact lt_last_of_mem_strict_append_singleton htail hy

theorem bump?_eq_none_of_strict_append_singleton {pre : Row} {x : ℕ}
    (hstrict : Row.Strict (pre ++ [x])) :
    Row.bump? x pre = none := by
  apply List.find?_eq_none.2
  intro y hy
  simpa using Nat.not_le_of_lt (lt_last_of_mem_strict_append_singleton hstrict hy)

theorem insert_of_popLast?_eq_some {row row' : Row} {x : ℕ}
    (hrow : Row.Strict row) (h : popLast? row = some (x, row')) :
    Row.insert x row' = ⟨row, none⟩ := by
  have happend : row = row' ++ [x] := eq_append_singleton_of_popLast?_eq_some h
  have hbump : Row.bump? x row' = none := by
    apply bump?_eq_none_of_strict_append_singleton
    simpa [happend] using hrow
  unfold Row.insert
  rw [hbump]
  simp [Row.inserted_eq_append_of_bump_none hbump, happend]

theorem strict_of_popLast?_eq_some {row row' : Row} {x : ℕ}
    (hrow : Row.Strict row) (h : popLast? row = some (x, row')) :
    Row.Strict row' := by
  have happend : row = row' ++ [x] := eq_append_singleton_of_popLast?_eq_some h
  have hpair : List.Pairwise (· < ·) (row' ++ [x]) := by
    simpa [Row.Strict, List.sortedLT_iff_pairwise, happend] using hrow
  simpa [Row.Strict, List.sortedLT_iff_pairwise] using (List.pairwise_append.1 hpair).1

/-- Reverse one row-bump step: given the bumped value `y` coming from below, replace the rightmost
entry `< y` by `y` and return the displaced entry. -/
def unbump? (y : ℕ) : Row → Option (ℕ × Row)
  | [] => none
  | [x] =>
      if x < y then
        some (x, [y])
      else
        none
  | x :: z :: row =>
      if z < y then
        match unbump? y (z :: row) with
        | none => none
        | some (x', row') => some (x', x :: row')
      else if x < y then
        some (x, y :: z :: row)
      else
        none

theorem unbump?_append_between :
    ∀ (as bs : Row) (x y : ℕ),
      (∀ a ∈ as, a < y) →
      x < y →
      (∀ b ∈ bs, y < b) →
      unbump? y (as ++ x :: bs) = some (x, as ++ y :: bs)
  | [], [], x, y, _, hxy, _ => by
      simp [unbump?, hxy]
  | [], b :: bs, x, y, _, hxy, hbs => by
      have hby : ¬ b < y := Nat.not_lt.mpr (Nat.le_of_lt (hbs b (by simp)))
      simp [unbump?, hxy, hby]
  | a :: as, bs, x, y, has, hxy, hbs => by
      cases as with
      | nil =>
          have htail := unbump?_append_between [] bs x y (by intro b hb; cases hb) hxy hbs
          have htail' : unbump? y (x :: bs) = some (x, y :: bs) := by
            simpa using htail
          simpa [unbump?, hxy] using
            congrArg
              (fun t =>
                match t with
                | none => none
                | some (x', row') => some (x', a :: row')) htail'
      | cons c as' =>
          have htailAss : ∀ d ∈ c :: as', d < y := by
            intro d hd
            exact has d (by simp [hd])
          have htail := unbump?_append_between (c :: as') bs x y htailAss hxy hbs
          have htail' : unbump? y (c :: (as' ++ x :: bs)) = some (x, c :: as' ++ y :: bs) := by
            simpa using htail
          have hcy : c < y := has c (by simp)
          simpa [unbump?, hcy] using
            congrArg
              (fun t =>
                match t with
                | none => none
                | some (x', row') => some (x', a :: row')) htail'

theorem unbump?_some_of_exists_lt :
    ∀ {row : Row} {y : ℕ},
      Row.Strict row → (∃ x ∈ row, x < y) → ∃ x' row', unbump? y row = some (x', row')
  | [], _, _, hlt => by
      rcases hlt with ⟨x, hx, _⟩
      cases hx
  | [x], y, _, hlt => by
      rcases hlt with ⟨x', hx', hxlt⟩
      simp at hx'
      subst x'
      exact ⟨x, [y], by simp [unbump?, hxlt]⟩
  | x :: z :: row, y, hstrict, hlt => by
      have hstrict' : Row.Strict (z :: row) := by
        rw [Row.Strict, List.sortedLT_iff_pairwise] at hstrict ⊢
        exact (List.pairwise_cons.1 hstrict).2
      by_cases hz : z < y
      ·
        have htail : ∃ x' ∈ z :: row, x' < y := ⟨z, by simp, hz⟩
        rcases unbump?_some_of_exists_lt hstrict' htail with ⟨x', row', hrec⟩
        exact ⟨x', x :: row', by simp [unbump?, hz, hrec]⟩
      ·
        by_cases hx : x < y
        · exact ⟨x, y :: z :: row, by simp [unbump?, hz, hx]⟩
        ·
          rcases hlt with ⟨w, hw, hwy⟩
          rcases List.mem_cons.1 hw with rfl | hw
          · exact False.elim (hx hwy)
          ·
            rcases List.mem_cons.1 hw with rfl | hw
            · exact False.elim (hz hwy)
            ·
              have hpair : List.Pairwise (· < ·) (x :: z :: row) := by
                simpa [Row.Strict, List.sortedLT_iff_pairwise] using hstrict
              have htail : List.Pairwise (· < ·) (z :: row) :=
                (List.pairwise_cons.1 hpair).2
              have hzw : z < w := (List.pairwise_cons.1 htail).1 _ hw
              exact False.elim (hz (lt_trans hzw hwy))

theorem unbump?_mem_of_eq_some :
    ∀ {row : Row} {y x : ℕ} {row' : Row},
      unbump? y row = some (x, row') → x ∈ row
  | [], _, _, _, h => by
      simp [unbump?] at h
  | [z], y, x, row', h => by
      by_cases hzy : z < y
      · simp [unbump?, hzy] at h
        rcases h with ⟨rfl, rfl⟩
        simp
      · simp [unbump?, hzy] at h
  | z₀ :: z₁ :: row, y, x, row', h => by
      by_cases hz₁ : z₁ < y
      ·
        cases hrec : unbump? y (z₁ :: row) with
        | none =>
            simp [unbump?, hz₁, hrec] at h
        | some p =>
            rcases p with ⟨x', row''⟩
            simp [unbump?, hz₁, hrec] at h
            rcases h with ⟨rfl, rfl⟩
            exact List.mem_cons_of_mem _ (unbump?_mem_of_eq_some hrec)
      ·
        by_cases hz₀ : z₀ < y
        · simp [unbump?, hz₁, hz₀] at h
          rcases h with ⟨rfl, rfl⟩
          simp
        · simp [unbump?, hz₁, hz₀] at h

theorem length_of_unbump?_eq_some :
    ∀ {row : Row} {y x : ℕ} {row' : Row},
      unbump? y row = some (x, row') → row'.length = row.length
  | [], _, _, _, h => by
      simp [unbump?] at h
  | [z], y, x, row', h => by
      by_cases hzy : z < y
      · simp [unbump?, hzy] at h
        rcases h with ⟨rfl, rfl⟩
        simp
      · simp [unbump?, hzy] at h
  | z₀ :: z₁ :: row, y, x, row', h => by
      by_cases hz₁ : z₁ < y
      ·
        cases hrec : unbump? y (z₁ :: row) with
        | none =>
            simp [unbump?, hz₁, hrec] at h
        | some p =>
            rcases p with ⟨x', row''⟩
            simp [unbump?, hz₁, hrec] at h
            rcases h with ⟨rfl, rfl⟩
            simpa using congrArg Nat.succ (length_of_unbump?_eq_some hrec)
      ·
        by_cases hz₀ : z₀ < y
        · simp [unbump?, hz₁, hz₀] at h
          rcases h with ⟨rfl, rfl⟩
          simp
        · simp [unbump?, hz₁, hz₀] at h

theorem unbump?_eq_some_iff_append :
    ∀ {row row' : Row} {x y : ℕ},
      Row.Strict row → y ∉ row → unbump? y row = some (x, row') →
      ∃ as bs,
        row = as ++ x :: bs ∧
        row' = as ++ y :: bs ∧
        (∀ a ∈ as, a < x) ∧
        x < y ∧
        (∀ b ∈ bs, y < b)
  | [], _, _, _, _, hy, _ => by
      simp [unbump?] at *
  | [z], row', x, y, _, hy, h => by
      have hzy : z < y := by
        by_cases hz : z < y
        · exact hz
        · simp [unbump?, hz] at h
      simp [unbump?, hzy] at h
      rcases h with ⟨rfl, rfl⟩
      refine ⟨[], [], by simp, by simp, ?_, hzy, ?_⟩
      · intro a ha
        cases ha
      · intro b hb
        cases hb
  | z₀ :: z₁ :: row, row', x, y, hstrict, hy, h => by
      have hpair : List.Pairwise (· < ·) (z₀ :: z₁ :: row) := by
        simpa [Row.Strict, List.sortedLT_iff_pairwise] using hstrict
      have hheadTail : ∀ w ∈ z₁ :: row, z₀ < w := (List.pairwise_cons.1 hpair).1
      have hpairTail : List.Pairwise (· < ·) (z₁ :: row) := (List.pairwise_cons.1 hpair).2
      have hstrictTail : Row.Strict (z₁ :: row) := by
        simpa [Row.Strict, List.sortedLT_iff_pairwise] using hpairTail
      have hyTail : y ∉ z₁ :: row := by
        intro hy'
        exact hy (by simp [hy'])
      by_cases hz₁ : z₁ < y
      ·
        cases hrec : unbump? y (z₁ :: row) with
        | none =>
            simp [unbump?, hz₁, hrec] at h
        | some p =>
            rcases p with ⟨x', row''⟩
            simp [unbump?, hz₁, hrec] at h
            rcases h with ⟨rfl, rfl⟩
            rcases unbump?_eq_some_iff_append hstrictTail hyTail hrec with
              ⟨as, bs, hrow, hrow', hprefix, hxy, hsuffix⟩
            have hxmem : x' ∈ z₁ :: row := unbump?_mem_of_eq_some hrec
            have hz₀x : z₀ < x' := hheadTail x' hxmem
            refine ⟨z₀ :: as, bs, ?_, ?_, ?_, hxy, hsuffix⟩
            · simpa [hrow, List.cons_append, List.append_assoc]
            · simpa [hrow', List.cons_append, List.append_assoc]
            ·
              intro a ha
              rcases List.mem_cons.1 ha with rfl | ha
              · exact hz₀x
              · exact hprefix _ ha
      ·
        by_cases hz₀ : z₀ < y
        ·
          simp [unbump?, hz₁, hz₀] at h
          rcases h with ⟨rfl, rfl⟩
          have hy_ne_z₁ : y ≠ z₁ := by
            intro hyz₁
            exact hy (by simp [hyz₁])
          have hyz₁ : y < z₁ := lt_of_le_of_ne (Nat.le_of_not_gt hz₁) hy_ne_z₁
          have hsuffix : ∀ b ∈ z₁ :: row, y < b := by
            intro b hb
            rcases List.mem_cons.1 hb with rfl | hb
            · exact hyz₁
            ·
              have hz₁b : z₁ < b := (List.pairwise_cons.1 hpairTail).1 _ hb
              exact lt_trans hyz₁ hz₁b
          refine ⟨[], z₁ :: row, by simp, by simp, ?_, hz₀, hsuffix⟩
          intro a ha
          cases ha
        ·
          simp [unbump?, hz₁, hz₀] at h

theorem unbump?_insert_of_eq_some {row row' : Row} {x y : ℕ}
    (hrow : Row.Strict row) (hy : y ∉ row)
    (h : Row.unbump? y row = some (x, row')) :
    Row.insert x row' = ⟨row, some y⟩ := by
  rcases Row.unbump?_eq_some_iff_append hrow hy h with
    ⟨as, bs, hrow_eq, hrow'_eq, hprefix, hxy, _⟩
  have hbump : Row.bump? x row' = some y := by
    rw [hrow'_eq]
    exact (Row.bump?_eq_some_iff_append.2
      ⟨Nat.le_of_lt hxy, as, bs, rfl, by
        intro a ha
        exact Nat.not_le_of_lt (hprefix a ha)⟩)
  have hins : Row.inserted x row' = as ++ x :: y :: bs := by
    rw [hrow'_eq, Row.inserted_eq_append_of_prefix_lt hprefix (Nat.le_of_lt hxy)]
  have hy_notin_as : y ∉ as := by
    intro hyas
    exact (Nat.lt_asymm (hprefix y hyas) hxy).elim
  unfold Row.insert
  rw [hbump, hins, hrow_eq]
  simp
  calc
    (as ++ x :: y :: bs).erase y = as ++ (x :: y :: bs).erase y := by
      rw [List.erase_append_right _ hy_notin_as]
    _ = as ++ x :: bs := by
      simp [hxy.ne]

theorem strict_of_unbump?_eq_some {row row' : Row} {x y : ℕ}
    (hrow : Row.Strict row) (hy : y ∉ row)
    (h : Row.unbump? y row = some (x, row')) :
    Row.Strict row' := by
  rcases Row.unbump?_eq_some_iff_append hrow hy h with
    ⟨as, bs, hrow_eq, hrow'_eq, hprefix, hxy, hsuffix⟩
  have hpair : List.Pairwise (· < ·) (as ++ x :: bs) := by
    simpa [Row.Strict, List.sortedLT_iff_pairwise, hrow_eq] using hrow
  have has : List.Pairwise (· < ·) as := (List.pairwise_append.1 hpair).1
  have htail : List.Pairwise (· < ·) (x :: bs) := (List.pairwise_append.1 hpair).2.1
  have hbs : List.Pairwise (· < ·) bs := (List.pairwise_cons.1 htail).2
  have hprefix' : ∀ a ∈ as, a < y := by
    intro a ha
    exact lt_trans (hprefix a ha) hxy
  have hpair' : List.Pairwise (· < ·) (as ++ y :: bs) := by
    rw [List.pairwise_append]
    refine ⟨has, ?_, ?_⟩
    · exact List.pairwise_cons.2 ⟨hsuffix, hbs⟩
    ·
      intro a ha b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact hprefix' a ha
      · exact lt_trans (hprefix' a ha) (hsuffix b hb)
  simpa [Row.Strict, List.sortedLT_iff_pairwise, hrow'_eq] using hpair'

theorem popLast?_insert_of_bump_none {x : ℕ} {row : Row}
    (h : Row.bump? x row = none) :
    popLast? (Row.insert x row).row = some (x, row) := by
  rw [Row.insert_eq_append_of_bump_none h]
  simpa using popLast?_append_singleton row x

theorem unbump?_insert_of_bump {x y : ℕ} {row : Row}
    (hrow : Row.Strict row) (hx : x ∉ row) (h : Row.bump? x row = some y) :
    unbump? y (Row.insert x row).row = some (x, row) := by
  rcases Row.insert_eq_append_of_bump hrow hx h with ⟨as, bs, hr, hins, hprefix, hxy⟩
  have hprefix' : ∀ a ∈ as, a < y := by
    intro a ha
    exact lt_trans (hprefix a ha) hxy
  have hpair : List.Pairwise (· < ·) (as ++ y :: bs) := by
    simpa [Row.Strict, List.sortedLT_iff_pairwise, hr] using hrow
  have hpair_tail : List.Pairwise (· < ·) (y :: bs) := by
    exact (List.pairwise_append.1 hpair).2.1
  have hsuffix : ∀ b ∈ bs, y < b := by
    intro b hb
    exact hpair_tail.rel_head_tail (by simpa using hb)
  rw [hins, hr]
  exact unbump?_append_between as bs x y hprefix' hxy hsuffix

end Row

theorem row_eq_append_singleton_of_strict_mem_max :
    ∀ {row : Row} {k : ℕ},
      Row.Strict row → k ∈ row → (∀ x ∈ row, x ≤ k) →
      ∃ pre, row = pre ++ [k] ∧ k ∉ pre
  | [], _, _, hk, _ => by
      cases hk
  | [a], k, _, hk, _ => by
      simp at hk
      subst hk
      exact ⟨[], by simp, by simp⟩
  | a :: b :: row, k, hstrict, hk, hmax => by
      have hpair : List.Pairwise (· < ·) (a :: b :: row) := by
        simpa [Row.Strict, List.sortedLT_iff_pairwise] using hstrict
      have hstrictTail : Row.Strict (b :: row) := by
        simpa [Row.Strict, List.sortedLT_iff_pairwise] using (List.pairwise_cons.1 hpair).2
      rcases List.mem_cons.1 hk with hka | hk
      ·
        subst hka
        have hkb' : k < b := (List.pairwise_cons.1 hpair).1 _ (by simp)
        have hbk : b ≤ k := hmax b (by simp)
        exact False.elim (Nat.not_le_of_lt hkb' hbk)
      ·
        have hmaxTail : ∀ x ∈ b :: row, x ≤ k := by
          intro x hx
          exact hmax x (by simp [hx])
        rcases row_eq_append_singleton_of_strict_mem_max hstrictTail hk hmaxTail with
          ⟨pre, htail, hknot⟩
        have hak : a < k := by
          have hkmem : k ∈ b :: row := by simpa [htail]
          exact (List.pairwise_cons.1 hpair).1 _ hkmem
        refine ⟨a :: pre, ?_, ?_⟩
        · simpa [htail, List.cons_append, List.append_assoc]
        ·
          intro hk'
          rcases List.mem_cons.1 hk' with hka' | hk'
          ·
            subst hka'
            exact (Nat.lt_irrefl _ hak).elim
          · exact hknot hk'

theorem isRSTableau_tail_of_cons_cons {upper lower : Row} {rows : List Row}
    (hT : IsRSTableau (upper :: lower :: rows)) :
    IsRSTableau (lower :: rows) := by
  rcases hT with ⟨hnonempty, hstrict, hshape, hcol⟩
  refine ⟨?_, ?_, shapeSorted_tail_of_cons hshape, ?_⟩
  ·
    intro r hr
    exact hnonempty r (by simp [hr])
  ·
    intro r hr
    exact hstrict r (by simp [hr])
  ·
    exact (columnStrict_cons_cons_iff (upper := upper) (lower := lower) (rows := rows)).1 hcol |>.2

theorem exists_mem_lt_of_columnStrictTwoRows {upper lower : Row} {y : ℕ}
    (hcol : ColumnStrictTwoRows upper lower)
    (hlen : lower.length ≤ upper.length)
    (hy : y ∈ lower) :
    ∃ x ∈ upper, x < y := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  have hj' : j < upper.length := lt_of_lt_of_le hj hlen
  refine ⟨upper[j], List.getElem_mem hj', ?_⟩
  simpa [Row.entry_eq_getElem lower hj, Row.entry_eq_getElem upper hj'] using hcol j hj

theorem columnStrictTwoRows_of_popLast_upper
    {upper lower upper' : Row} {x : ℕ}
    (hcol : ColumnStrictTwoRows upper lower)
    (hlen : lower.length ≤ upper'.length)
    (hpop : Row.popLast? upper = some (x, upper')) :
    ColumnStrictTwoRows upper' lower := by
  have hupper : upper = upper' ++ [x] := Row.eq_append_singleton_of_popLast?_eq_some hpop
  intro j hj
  have hj' : j < upper'.length := lt_of_lt_of_le hj hlen
  calc
    upper'.entry j = upper.entry j := by
      rw [hupper]
      symm
      exact Row.entry_append_left _ _ hj'
    _ < lower.entry j := hcol j hj

theorem columnStrictTwoRows_of_unbump_upper_popLast_lower
    {upper lower upper' lower' : Row} {x y : ℕ}
    (hcol : ColumnStrictTwoRows upper lower)
    (hlen : lower.length ≤ upper.length)
    (hupper : Row.Strict upper)
    (hlower : Row.Strict lower)
    (hy : y ∉ upper)
    (hunbump : Row.unbump? y upper = some (x, upper'))
    (hpop : Row.popLast? lower = some (y, lower')) :
    ColumnStrictTwoRows upper' lower' := by
  rcases Row.unbump?_eq_some_iff_append hupper hy hunbump with
    ⟨as, bs, hupper_eq, hupper'_eq, hprefix, hxy, hsuffix⟩
  have hlower_eq : lower = lower' ++ [y] := Row.eq_append_singleton_of_popLast?_eq_some hpop
  have hlower'_le : lower'.length ≤ as.length := by
    by_contra hgt
    have hgt' : as.length < lower'.length := Nat.lt_of_not_ge hgt
    have hj : as.length + 1 < lower.length := by
      simpa [hlower_eq, List.length_append] using Nat.succ_lt_succ hgt'
    have hju : as.length + 1 < upper.length := lt_of_lt_of_le hj hlen
    have hbspos : 0 < bs.length := by
      rw [hupper_eq] at hju
      simp [List.length_append] at hju
      omega
    have hy_upper : y < upper.entry (as.length + 1) := by
      have hmem : Row.entry bs 0 ∈ bs := by
        rw [Row.entry_eq_getElem bs hbspos]
        exact List.getElem_mem hbspos
      have hu_eq : upper.entry (as.length + 1) = Row.entry bs 0 := by
        rw [hupper_eq]
        simpa [Row.entry] using
          (Row.entry_append_right as (x :: bs) (j := as.length + 1) (by omega))
      rw [hu_eq]
      exact hsuffix _ hmem
    have hy_lower : lower.entry (as.length + 1) ≤ y := by
      rw [hlower_eq]
      by_cases hj' : as.length + 1 < lower'.length
      ·
        have hmem : lower'.entry (as.length + 1) ∈ lower' := by
          rw [Row.entry_eq_getElem lower' hj']
          exact List.getElem_mem hj'
        have hl_eq :
            (lower' ++ [y]).entry (as.length + 1) = lower'.entry (as.length + 1) := by
          exact Row.entry_append_left lower' [y] (j := as.length + 1) hj'
        rw [hl_eq]
        exact Nat.le_of_lt <|
          Row.lt_last_of_mem_strict_append_singleton (pre := lower') (x := y)
            (by simpa [hlower_eq] using hlower) hmem
      ·
        have heq : as.length + 1 = lower'.length := by
          omega
        rw [heq]
        simpa [hlower_eq, Row.entry] using
          (Row.entry_append_right lower' [y] (j := lower'.length) (Nat.le_refl _))
    exact (Nat.lt_asymm hy_upper (lt_of_lt_of_le (hcol (as.length + 1) hj) hy_lower)).elim
  intro j hj
  have hj' : j < as.length := lt_of_lt_of_le hj hlower'_le
  calc
    upper'.entry j = upper.entry j := by
      rw [hupper'_eq, hupper_eq]
      simp [Row.entry_append_left, hj']
    _ < lower.entry j := by
      have hjl : j < lower.length := by
        exact lt_of_lt_of_le hj (by simpa [hlower_eq] using Nat.le_succ j)
      exact hcol j hjl
    _ = lower'.entry j := by
      symm
      simpa [hlower_eq] using (Row.entry_append_left lower' [y] (j := j) hj).symm

theorem columnStrictTwoRows_of_unbump_upper_unbump_lower
    {upper lower upper' lower' : Row} {x y z : ℕ}
    (hcol : ColumnStrictTwoRows upper lower)
    (hlen : lower.length ≤ upper.length)
    (hupper : Row.Strict upper)
    (hlower : Row.Strict lower)
    (hy : y ∉ upper)
    (hz : z ∉ lower)
    (hunbumpU : Row.unbump? y upper = some (x, upper'))
    (hunbumpL : Row.unbump? z lower = some (y, lower')) :
    ColumnStrictTwoRows upper' lower' := by
  rcases Row.unbump?_eq_some_iff_append hupper hy hunbumpU with
    ⟨as, bs, hupper_eq, hupper'_eq, hprefixU, hxy, hsuffixU⟩
  rcases Row.unbump?_eq_some_iff_append hlower hz hunbumpL with
    ⟨cs, ds, hlower_eq, hlower'_eq, hprefixL, hyz, hsuffixL⟩
  have hcsle : cs.length ≤ as.length := by
    by_contra hgt
    have hgt' : as.length < cs.length := Nat.lt_of_not_ge hgt
    have hj : as.length + 1 < lower.length := by
      rw [hlower_eq]
      simp [List.length_append]
      omega
    have hju : as.length + 1 < upper.length := lt_of_lt_of_le hj hlen
    have hbspos : 0 < bs.length := by
      rw [hupper_eq] at hju
      simp [List.length_append] at hju
      omega
    have hy_upper : y < upper.entry (as.length + 1) := by
      have hmem : Row.entry bs 0 ∈ bs := by
        rw [Row.entry_eq_getElem bs hbspos]
        exact List.getElem_mem hbspos
      have hu_eq : upper.entry (as.length + 1) = Row.entry bs 0 := by
        rw [hupper_eq]
        simpa [Row.entry] using
          (Row.entry_append_right as (x :: bs) (j := as.length + 1) (by omega))
      rw [hu_eq]
      exact hsuffixU _ hmem
    have hy_lower : lower.entry (as.length + 1) ≤ y := by
      rw [hlower_eq]
      by_cases hj' : as.length + 1 < cs.length
      ·
        have hmem : cs.entry (as.length + 1) ∈ cs := by
          rw [Row.entry_eq_getElem cs hj']
          exact List.getElem_mem hj'
        have hl_eq :
            (cs ++ y :: ds).entry (as.length + 1) = cs.entry (as.length + 1) := by
          exact Row.entry_append_left cs (y :: ds) (j := as.length + 1) hj'
        rw [hl_eq]
        exact Nat.le_of_lt (hprefixL _ hmem)
      ·
        have heq : as.length + 1 = cs.length := by
          omega
        rw [heq]
        simpa [hlower_eq, Row.entry] using
          (Row.entry_append_right cs (y :: ds) (j := cs.length) (Nat.le_refl _))
    exact (Nat.lt_asymm hy_upper (lt_of_lt_of_le (hcol (as.length + 1) hj) hy_lower)).elim
  have hlen' : lower'.length = lower.length := by
    simpa using Row.length_of_unbump?_eq_some hunbumpL
  intro j hj
  by_cases hjcs : j < cs.length
  ·
    have hjas : j < as.length := lt_of_lt_of_le hjcs hcsle
    calc
      upper'.entry j = upper.entry j := by
        rw [hupper'_eq, hupper_eq]
        simp [Row.entry_append_left, hjas]
      _ < lower.entry j := by
        exact hcol j (by simpa [hlen'] using hj)
      _ = lower'.entry j := by
        rw [hlower'_eq, hlower_eq]
        simp [Row.entry_append_left, hjcs]
  ·
    have hjle : cs.length ≤ j := Nat.le_of_not_gt hjcs
    rcases eq_or_lt_of_le hjle with hjeq | hjgt
    ·
      have hjeq' : j = cs.length := hjeq.symm
      by_cases hjas : cs.length < as.length
      ·
        have hy_lower : lower.entry cs.length = y := by
          rw [hlower_eq]
          rw [Row.entry_append_right _ _ (Nat.le_refl _)]
          simp [Row.entry]
        calc
          upper'.entry j = upper.entry j := by
            rw [hjeq']
            rw [hupper'_eq, hupper_eq]
            simp [Row.entry_append_left, hjas]
          _ < lower.entry j := by
            have hjl : cs.length < lower.length := by
              rw [← hjeq']
              simpa [hlen'] using hj
            rw [hjeq']
            exact hcol cs.length hjl
          _ = y := by simpa [hjeq'] using hy_lower
          _ < z := hyz
          _ = lower'.entry j := by
            rw [hjeq']
            rw [hlower'_eq]
            rw [Row.entry_append_right _ _ (Nat.le_refl _)]
            simp [Row.entry]
      ·
        have hceq : cs.length = as.length := le_antisymm hcsle (Nat.le_of_not_gt hjas)
        calc
          upper'.entry j = y := by
            rw [hjeq', hceq]
            rw [hupper'_eq]
            rw [Row.entry_append_right _ _ (Nat.le_refl _)]
            simp [Row.entry]
          _ < z := hyz
          _ = lower'.entry j := by
            rw [hjeq']
            rw [hlower'_eq]
            rw [Row.entry_append_right _ _ (Nat.le_refl _)]
            simp [Row.entry]
    ·
      by_cases hjas : j < as.length
      ·
        calc
          upper'.entry j = upper.entry j := by
            rw [hupper'_eq, hupper_eq]
            simp [Row.entry_append_left, hjas]
          _ < lower.entry j := by
            exact hcol j (by simpa [hlen'] using hj)
          _ = lower'.entry j := by
            rw [hlower'_eq, hlower_eq]
            rw [Row.entry_append_right _ _ (Nat.le_of_lt hjgt)]
            rw [Row.entry_append_right _ _ (Nat.le_of_lt hjgt)]
            have hk : j - cs.length = j - (cs.length + 1) + 1 := by omega
            rw [hk]
            simp [Row.entry]
      ·
        by_cases hjeqas : j = as.length
        ·
          have hcslt : cs.length < as.length := by
            apply lt_of_le_of_ne hcsle
            intro h
            have : cs.length < cs.length := by
              simpa [h, hjeqas] using hjgt
            exact (Nat.lt_irrefl _ this).elim
          have hjds : as.length - (cs.length + 1) < ds.length := by
            rw [hlower'_eq] at hj
            simp [List.length_append] at hj
            omega
          have hmem : Row.entry ds (as.length - (cs.length + 1)) ∈ ds := by
            rw [Row.entry_eq_getElem ds hjds]
            exact List.getElem_mem hjds
          have hl_eq : lower.entry as.length = Row.entry ds (as.length - (cs.length + 1)) := by
            rw [hlower_eq]
            rw [Row.entry_append_right _ _ (Nat.le_of_lt hcslt)]
            have hk : as.length - cs.length = as.length - (cs.length + 1) + 1 := by omega
            rw [hk]
            simp [Row.entry]
          have hz_lower : z < lower.entry as.length := by
            rw [hl_eq]
            exact hsuffixL _ hmem
          calc
            upper'.entry j = y := by
              rw [hjeqas]
              rw [hupper'_eq]
              rw [Row.entry_append_right _ _ (Nat.le_refl _)]
              simp [Row.entry]
            _ < z := hyz
            _ < lower.entry j := by simpa [hjeqas] using hz_lower
            _ = lower'.entry j := by
              rw [hlower'_eq, hlower_eq]
              rw [hjeqas]
              rw [Row.entry_append_right _ _ (Nat.le_of_lt hcslt)]
              rw [Row.entry_append_right _ _ (Nat.le_of_lt hcslt)]
              have hk : as.length - cs.length = as.length - (cs.length + 1) + 1 := by omega
              rw [hk]
              simp [Row.entry]
        ·
          have haslt : as.length < j := by
            apply lt_of_le_of_ne (Nat.le_of_not_gt hjas)
            intro h
            exact hjeqas h.symm
          calc
            upper'.entry j = upper.entry j := by
              have hU' : upper'.entry j = Row.entry bs (j - (as.length + 1)) := by
                rw [hupper'_eq]
                rw [Row.entry_append_right _ _ (Nat.le_of_lt haslt)]
                have hk : j - as.length = j - (as.length + 1) + 1 := by omega
                rw [hk]
                simp [Row.entry]
              have hU : upper.entry j = Row.entry bs (j - (as.length + 1)) := by
                rw [hupper_eq]
                rw [Row.entry_append_right _ _ (Nat.le_of_lt haslt)]
                have hk : j - as.length = j - (as.length + 1) + 1 := by omega
                rw [hk]
                simp [Row.entry]
              rw [hU', hU]
            _ < lower.entry j := by
              exact hcol j (by simpa [hlen'] using hj)
            _ = lower'.entry j := by
              rw [hlower'_eq, hlower_eq]
              rw [Row.entry_append_right _ _ (Nat.le_of_lt hjgt)]
              rw [Row.entry_append_right _ _ (Nat.le_of_lt hjgt)]
              have hk : j - cs.length = j - (cs.length + 1) + 1 := by omega
              rw [hk]
              simp [Row.entry]

theorem columnStrictTwoRows_of_unbump_upper_singleton_lower
    {upper upper' next : Row} {x y : ℕ}
    (hpair₁ : ColumnStrictTwoRows upper [y])
    (hpair₂ : ColumnStrictTwoRows [y] next)
    (hupper : Row.Strict upper)
    (hy : y ∉ upper)
    (hunbump : Row.unbump? y upper = some (x, upper'))
    (hlen : next.length ≤ 1) :
    ColumnStrictTwoRows upper' next := by
  rcases Row.unbump?_eq_some_iff_append hupper hy hunbump with
    ⟨as, bs, hupper_eq, hupper'_eq, hprefix, hxy, hsuffix⟩
  intro j hj
  have hj0 : j = 0 := by omega
  subst hj0
  cases as with
  | nil =>
      calc
        upper'.entry 0 = y := by
          rw [hupper'_eq]
          simp [Row.entry]
        _ < next.entry 0 := hpair₂ 0 (by simpa using hj)
  | cons a as' =>
      calc
        upper'.entry 0 = upper.entry 0 := by
          rw [hupper'_eq, hupper_eq]
          simp [Row.entry]
        _ < Row.entry [y] 0 := hpair₁ 0 (by simp)
        _ = y := by simp [Row.entry]
        _ < next.entry 0 := hpair₂ 0 (by simpa using hj)

/-- Remove the last cell from the `i`-th row of a tableau, dropping that row if it becomes empty. -/
def popCellAt : ℕ → List Row → Option (ℕ × List Row)
  | 0, [] => none
  | 0, row :: rows =>
      match Row.popLast? row with
      | none => none
      | some (x, row') =>
          if hnil : row' = [] then
            some (x, rows)
          else
            some (x, row' :: rows)
  | i + 1, [] => none
  | i + 1, row :: rows =>
      match popCellAt i rows with
      | none => none
      | some (x, rows') => some (x, row :: rows')

/-- Reverse `insertRows`: starting from the row index where the new cell was created, undo the
propagated bump chain and recover the original inserted value together with the previous tableau. -/
def reverseInsertRowsAt : ℕ → List Row → Option (ℕ × List Row)
  | 0, [] => none
  | 0, row :: rows =>
      match Row.popLast? row with
      | none => none
      | some (x, row') =>
          if hnil : row' = [] then
            some (x, rows)
          else
            some (x, row' :: rows)
  | i + 1, [] => none
  | i + 1, row :: rows =>
      match reverseInsertRowsAt i rows with
      | none => none
      | some (y, rows') =>
          match Row.unbump? y row with
          | none => none
          | some (x, row') => some (x, row' :: rows')

/-- Remove the label `k` from the unique row where `recordAt k` appended it, returning the row
index and the previous row-list if successful. -/
def unrecordAt (k : ℕ) : List Row → Option (ℕ × List Row)
  | [] => none
  | row :: rows =>
      if hk : k ∈ row then
        let row' := row.erase k
        if hnil : row' = [] then
          some (0, rows)
        else
          some (0, row' :: rows)
      else
        match unrecordAt k rows with
        | none => none
        | some (i, rows') => some (i + 1, row :: rows')

theorem erase_append_singleton_of_not_mem {k : ℕ} :
    ∀ {row : Row}, k ∉ row → (row ++ [k]).erase k = row
  | [], _ => by
      simp
  | a :: row, hk => by
      have hka : a ≠ k := by
        intro hka
        exact hk (by simp [hka])
      have hktail : k ∉ row := by
        intro hmem
        exact hk (by simp [hmem])
      simpa [List.erase, hka] using congrArg (List.cons a) (erase_append_singleton_of_not_mem hktail)

theorem not_mem_row_of_entriesLt {k : ℕ} {rows : List Row} {row : Row}
    (hlt : EntriesLt k rows) (hrow : row ∈ rows) :
    k ∉ row := by
  intro hk
  exact Nat.lt_irrefl _ (hlt row hrow k hk)

theorem unrecordAt_recordAt (k : ℕ) :
    ∀ i : ℕ, ∀ rows : List Row,
      RowsNonempty rows → EntriesLt k rows → i ≤ rows.length →
      unrecordAt k (recordAt k i rows) = some (i, rows)
  | 0, [], _, _, _ => by
      simp [unrecordAt, recordAt]
  | 0, row :: rows, hnonempty, hlt, _ => by
      have hknot : k ∉ row := not_mem_row_of_entriesLt hlt (by simp)
      have herase : (row ++ [k]).erase k = row := erase_append_singleton_of_not_mem hknot
      have hrowne : row ≠ [] := hnonempty row (by simp)
      have hmem : k ∈ row ++ [k] := by simp
      simp [unrecordAt, recordAt, hmem, hknot, herase, hrowne]
  | i + 1, [], _, _, hi => by
      cases hi
  | i + 1, row :: rows, hnonempty, hlt, hi => by
      have hknot : k ∉ row := not_mem_row_of_entriesLt hlt (by simp)
      have hnonempty_tail : RowsNonempty rows := by
        intro r hr
        exact hnonempty r (by simp [hr])
      have hlt_tail : EntriesLt k rows := by
        intro r hr x hx
        exact hlt r (by simp [hr]) x hx
      have hi' : i ≤ rows.length := Nat.le_of_succ_le_succ hi
      simp [unrecordAt, recordAt, hknot, unrecordAt_recordAt k i rows hnonempty_tail hlt_tail hi']

theorem unrecordAt_some_of_mem_flatten {k : ℕ} :
    ∀ {rows : List Row}, k ∈ rows.flatten → ∃ i rows', unrecordAt k rows = some (i, rows')
  | [], hk => by
      simp at hk
  | row :: rows, hk => by
      by_cases hkrow : k ∈ row
      · by_cases hnil : List.erase row k = []
        · exact ⟨0, rows, by simp [unrecordAt, hkrow, hnil]⟩
        · exact ⟨0, List.erase row k :: rows, by simp [unrecordAt, hkrow, hnil]⟩
      ·
        have hktail : k ∈ rows.flatten := by
          rcases List.mem_flatten.1 hk with ⟨r, hr, hkrow'⟩
          rcases List.mem_cons.1 hr with rfl | hr
          · exact False.elim (hkrow hkrow')
          · exact List.mem_flatten.2 ⟨r, hr, hkrow'⟩
        rcases unrecordAt_some_of_mem_flatten (rows := rows) hktail with ⟨i, rows', hrec⟩
        exact ⟨i + 1, row :: rows', by simp [unrecordAt, hkrow, hrec]⟩

theorem unrecordAt_index_lt_length {k : ℕ} :
    ∀ {rows : List Row} {i : ℕ} {rows' : List Row},
      unrecordAt k rows = some (i, rows') → i < rows.length
  | [], _, _, h => by
      simp [unrecordAt] at h
  | row :: rows, 0, rows', h => by
      by_cases hk : k ∈ row
      ·
        by_cases hnil : row.erase k = []
        · simp [unrecordAt, hk, hnil] at h
          simp
        · simp [unrecordAt, hk, hnil] at h
          simp
      ·
        cases hrec : unrecordAt k rows with
        | none =>
            simp [unrecordAt, hk, hrec] at h
        | some p =>
            rcases p with ⟨j, zs⟩
            simp [unrecordAt, hk, hrec] at h
  | row :: rows, i + 1, rows', h => by
      by_cases hk : k ∈ row
      ·
        by_cases hnil : row.erase k = []
        · simp [unrecordAt, hk, hnil] at h
        · simp [unrecordAt, hk, hnil] at h
      ·
        cases hrec : unrecordAt k rows with
        | none =>
            simp [unrecordAt, hk, hrec] at h
        | some p =>
            rcases p with ⟨j, zs⟩
            simp [unrecordAt, hk, hrec] at h
            rcases h with ⟨rfl, rfl⟩
            have hj : j < rows.length := unrecordAt_index_lt_length hrec
            exact Nat.succ_lt_succ hj

theorem unrecordAt_index_le_length_result {k : ℕ} :
    ∀ {rows : List Row} {i : ℕ} {rows' : List Row},
      unrecordAt k rows = some (i, rows') → i ≤ rows'.length
  | [], _, _, h => by
      simp [unrecordAt] at h
  | row :: rows, 0, rows', h => by
      by_cases hk : k ∈ row
      ·
        by_cases hnil : row.erase k = []
        · simp [unrecordAt, hk, hnil] at h
          omega
        · simp [unrecordAt, hk, hnil] at h
          omega
      ·
        cases hrec : unrecordAt k rows with
        | none =>
            simp [unrecordAt, hk, hrec] at h
        | some p =>
            rcases p with ⟨j, zs⟩
            simp [unrecordAt, hk, hrec] at h
  | row :: rows, i + 1, rows', h => by
      by_cases hk : k ∈ row
      ·
        by_cases hnil : row.erase k = []
        · simp [unrecordAt, hk, hnil] at h
        · simp [unrecordAt, hk, hnil] at h
      ·
        cases hrec : unrecordAt k rows with
        | none =>
            simp [unrecordAt, hk, hrec] at h
        | some p =>
            rcases p with ⟨j, zs⟩
            simp [unrecordAt, hk, hrec] at h
            rcases h with ⟨rfl, rfl⟩
            have hj : j ≤ zs.length := unrecordAt_index_le_length_result hrec
            exact Nat.succ_le_succ hj

theorem rowsNonempty_of_unrecordAt {k : ℕ} :
    ∀ {rows : List Row} {i : ℕ} {rows' : List Row},
      RowsNonempty rows →
      unrecordAt k rows = some (i, rows') →
      RowsNonempty rows'
  | [], _, _, hnonempty, h => by
      simp [unrecordAt] at h
  | row :: rows, 0, rows', hnonempty, h => by
      by_cases hk : k ∈ row
      ·
        by_cases hnil : row.erase k = []
        · simp [unrecordAt, hk, hnil] at h
          rcases h with rfl
          intro r hr
          exact hnonempty r (by simp [hr])
        · simp [unrecordAt, hk, hnil] at h
          rcases h with ⟨rfl, rfl⟩
          intro r hr
          rcases List.mem_cons.1 hr with rfl | hr
          · exact hnil
          · exact hnonempty r (by simp [hr])
      ·
        cases hrec : unrecordAt k rows with
        | none =>
            simp [unrecordAt, hk, hrec] at h
        | some p =>
            rcases p with ⟨j, zs⟩
            simp [unrecordAt, hk, hrec] at h
  | row :: rows, i + 1, rows', hnonempty, h => by
      by_cases hk : k ∈ row
      ·
        by_cases hnil : row.erase k = []
        · simp [unrecordAt, hk, hnil] at h
        · simp [unrecordAt, hk, hnil] at h
      ·
        cases hrec : unrecordAt k rows with
        | none =>
            simp [unrecordAt, hk, hrec] at h
        | some p =>
            rcases p with ⟨j, zs⟩
            simp [unrecordAt, hk, hrec] at h
            rcases h with ⟨rfl, rfl⟩
            have htail : RowsNonempty rows := by
              intro r hr
              exact hnonempty r (by simp [hr])
            have hzs : RowsNonempty zs := rowsNonempty_of_unrecordAt htail hrec
            intro r₁ hr₁
            rcases List.mem_cons.1 hr₁ with rfl | hr₁
            · exact hnonempty _ (by simp)
            · exact hzs r₁ hr₁

theorem head_ge_all_of_recordAt {k m : ℕ} :
    ∀ {i : ℕ} {rows : List Row},
      (∀ r ∈ recordAt k i rows, r.length ≤ m) →
      ∀ r ∈ rows, r.length ≤ m
  | 0, [], h, r, hr => by
      cases hr
  | 0, row :: rows, h, r, hr => by
      rcases List.mem_cons.1 hr with rfl | hr
      ·
        have hrow : (r ++ [k]).length ≤ m := h _ (by simp [recordAt])
        have hrow' : r.length + 1 ≤ m := by simpa using hrow
        omega
      · exact h _ (by simp [recordAt, hr])
  | i + 1, [], h, r, hr => by
      cases hr
  | i + 1, row :: rows, h, r, hr => by
      rcases List.mem_cons.1 hr with rfl | hr
      · exact h _ (by simp [recordAt])
      ·
        have htail : ∀ r ∈ recordAt k i rows, r.length ≤ m := by
          intro r hr'
          exact h r (by simp [recordAt, hr'])
        exact head_ge_all_of_recordAt htail r hr

theorem columnStrict_tail_of_cons {row : Row} {rows : List Row}
    (h : ColumnStrict (row :: rows)) :
    ColumnStrict rows := by
  intro i j hj
  simpa [ColumnStrict, Nat.add_assoc, List.getD_cons_succ] using h (i + 1) j hj

theorem isRSTableau_of_recordAt :
    ∀ {k i : ℕ} {rows : List Row},
      RowsNonempty rows →
      EntriesLt k rows →
      IsRSTableau (recordAt k i rows) →
      IsRSTableau rows
  | k, 0, [], hnonempty, hlt, hT => by
      refine ⟨?_, ?_, shapeSorted_nil, columnStrict_nil⟩
      · intro r hr
        cases hr
      · intro r hr
        cases hr
  | k, 0, row :: rows, hnonempty, hlt, hT => by
      rcases hT with ⟨hnonempty', hstrict', hshape', hcol'⟩
      refine ⟨hnonempty, ?_, ?_, ?_⟩
      ·
        intro r hr
        rcases List.mem_cons.1 hr with rfl | hr
        ·
          have hpop : Row.popLast? (r ++ [k]) = some (k, r) :=
            Row.popLast?_append_singleton r k
          have hr' : r ++ [k] ∈ recordAt k 0 (r :: rows) := by
            simp [recordAt]
          exact Row.strict_of_popLast?_eq_some (hstrict' _ hr') hpop
        ·
          have hr' : r ∈ recordAt k 0 (row :: rows) := by
            simp [recordAt, hr]
          exact hstrict' _ hr'
      ·
        cases rows with
        | nil =>
            simp [ShapeSorted, List.sortedGE_iff_pairwise]
        | cons lower tail =>
            have hshapeTail : ShapeSorted (lower :: tail) := shapeSorted_tail_of_cons hshape'
            have hpair : ColumnStrictTwoRows (row ++ [k]) lower :=
              columnStrictTwoRows_of_cons_cons hcol'
            have hlen0 : lower.length ≤ row.length := by
              have hlen1 : lower.length ≤ (row ++ [k]).length :=
                length_head_le_of_shapeSorted_cons_cons hshape'
              have hlen1' : lower.length ≤ row.length + 1 := by
                simpa using hlen1
              by_contra hgt
              have hgt' : row.length < lower.length := Nat.lt_of_not_ge hgt
              have hle' : row.length + 1 ≤ lower.length := Nat.succ_le_of_lt hgt'
              have heq : lower.length = row.length + 1 := Nat.le_antisymm hlen1' hle'
              have hklt : k < lower.entry row.length := by
                simpa [heq, Row.entry_append_right _ _ (Nat.le_refl _)] using
                  hpair row.length (by simpa [heq])
              have hmem : lower.entry row.length ∈ lower := by
                rw [Row.entry_eq_getElem lower (by simpa [heq])]
                exact List.getElem_mem (by simpa [heq])
              have hltLower : lower.entry row.length < k := hlt _ (by simp) _ hmem
              exact (Nat.lt_asymm hklt hltLower).elim
            apply shapeSorted_cons_of_head_ge_all hshapeTail
            intro r hr
            rcases List.mem_cons.1 hr with rfl | hr
            · exact hlen0
            · exact le_trans (head_ge_all_of_shapeSorted_cons hshapeTail r hr) hlen0
      ·
        cases rows with
        | nil =>
            exact columnStrict_singleton row
        | cons lower tail =>
            have hpair : ColumnStrictTwoRows (row ++ [k]) lower :=
              columnStrictTwoRows_of_cons_cons hcol'
            have hlen0 : lower.length ≤ row.length := by
              have hlen1 : lower.length ≤ (row ++ [k]).length :=
                length_head_le_of_shapeSorted_cons_cons hshape'
              have hlen1' : lower.length ≤ row.length + 1 := by
                simpa using hlen1
              by_contra hgt
              have hgt' : row.length < lower.length := Nat.lt_of_not_ge hgt
              have hle' : row.length + 1 ≤ lower.length := Nat.succ_le_of_lt hgt'
              have heq : lower.length = row.length + 1 := Nat.le_antisymm hlen1' hle'
              have hklt : k < lower.entry row.length := by
                simpa [heq, Row.entry_append_right _ _ (Nat.le_refl _)] using
                  hpair row.length (by simpa [heq])
              have hmem : lower.entry row.length ∈ lower := by
                rw [Row.entry_eq_getElem lower (by simpa [heq])]
                exact List.getElem_mem (by simpa [heq])
              have hltLower : lower.entry row.length < k := hlt _ (by simp) _ hmem
              exact (Nat.lt_asymm hklt hltLower).elim
            apply (columnStrict_cons_cons_iff (upper := row) (lower := lower) (rows := tail)).2
            refine ⟨?_, ?_⟩
            ·
              intro j hj
              have hjrow : j < row.length := lt_of_lt_of_le hj hlen0
              calc
                row.entry j = (row ++ [k]).entry j := by
                  symm
                  exact Row.entry_append_left _ _ hjrow
                _ < lower.entry j := hpair j hj
            ·
              exact (isRSTableau_tail_of_cons_cons
                ⟨hnonempty', hstrict', hshape', hcol'⟩).2.2.2
  | k, i + 1, [], hnonempty, hlt, hT => by
      simpa [recordAt] using hT
  | k, i + 1, row :: [], hnonempty, hlt, hT => by
      rcases hT with ⟨hnonempty', hstrict', hshape', hcol'⟩
      refine ⟨hnonempty, ?_, ?_, columnStrict_singleton row⟩
      ·
        intro r hr
        rcases List.mem_singleton.1 hr
        exact hstrict' _ (by simp [recordAt])
      · simp [ShapeSorted, List.sortedGE_iff_pairwise]
  | k, i + 1, row :: lower :: tail, hnonempty, hlt, hT => by
      have hTcons : IsRSTableau (row :: recordAt k i (lower :: tail)) := by
        simpa [recordAt] using hT
      rcases hTcons with ⟨hnonempty', hstrict', hshape', hcol'⟩
      have htailT : IsRSTableau (recordAt k i (lower :: tail)) := by
        refine ⟨?_, ?_, shapeSorted_tail_of_cons hshape', ?_⟩
        ·
          intro r hr
          exact hnonempty' r (by simp [hr])
        ·
          intro r hr
          exact hstrict' r (by simp [hr])
        ·
          exact columnStrict_tail_of_cons hcol'
      have htailNonempty : RowsNonempty (lower :: tail) := by
        intro r hr
        exact hnonempty r (by simp [hr])
      have hltTail : EntriesLt k (lower :: tail) := by
        intro r hr x hx
        exact hlt _ (by simp [hr]) _ hx
      have htailRST : IsRSTableau (lower :: tail) :=
        isRSTableau_of_recordAt htailNonempty hltTail htailT
      refine ⟨hnonempty, ?_, ?_, ?_⟩
      ·
        intro r hr
        rcases List.mem_cons.1 hr with rfl | hr
        · exact hstrict' _ (by simp)
        · exact htailRST.2.1 _ hr
      ·
        apply shapeSorted_cons_of_head_ge_all htailRST.2.2.1
        intro r hr
        have hhead' : ∀ r ∈ recordAt k i (lower :: tail), r.length ≤ row.length :=
          head_ge_all_of_shapeSorted_cons hshape'
        exact head_ge_all_of_recordAt hhead' r hr
      ·
        apply (columnStrict_cons_cons_iff (upper := row) (lower := lower) (rows := tail)).2
        refine ⟨?_, htailRST.2.2.2⟩
        intro j hj
        have hpair :
            ColumnStrictTwoRows row ((recordAt k i (lower :: tail)).getD 0 []) :=
          by
            intro j hj'
            simpa [ColumnStrict, ColumnStrictTwoRows, List.getD_cons_zero, List.getD_cons_succ] using
              hcol' 0 j hj'
        have hj' : j < ((recordAt k i (lower :: tail)).getD 0 []).length := by
          cases i with
          | zero =>
              simpa [recordAt] using Nat.lt_succ_of_lt hj
          | succ i =>
              simpa [recordAt] using hj
        calc
          row.entry j < ((recordAt k i (lower :: tail)).getD 0 []).entry j := hpair j hj'
          _ = lower.entry j := by
            cases i with
            | zero =>
                simp [recordAt, Row.entry_append_left, hj]
            | succ i =>
                simp [recordAt]

theorem recordAt_of_unrecordAt_max {k : ℕ} :
    ∀ {rows rows' : List Row} {i : ℕ},
      IsRSTableau rows → EntriesNodup rows →
      (∀ x ∈ rows.flatten, x ≤ k) → k ∈ rows.flatten →
      unrecordAt k rows = some (i, rows') →
      recordAt k i rows' = rows
  | [], _, _, hT, _, _, hk, _ => by
      simp at hk
  | row :: rows, rows', i, hT, hnd, hmax, hk, h => by
      rcases hT with ⟨hnonempty, hstrict, hshape, hcol⟩
      by_cases hkrow : k ∈ row
      ·
        have hrowmax : ∀ x ∈ row, x ≤ k := by
          intro x hx
          exact hmax x (List.mem_flatten_of_mem (by simp) hx)
        rcases row_eq_append_singleton_of_strict_mem_max
            (hstrict row (by simp)) hkrow hrowmax with ⟨pre, hroweq, hknotpre⟩
        have htail_not : k ∉ rows.flatten := not_mem_tail_flatten_of_mem_head hkrow hnd
        have herase : row.erase k = pre := by
          rw [hroweq]
          simpa using erase_append_singleton_of_not_mem (row := pre) hknotpre
        by_cases hpre : pre = []
        · subst hpre
          have hrowk : row = [k] := by simpa [hroweq]
          cases rows with
          | nil =>
              simp [unrecordAt, hkrow, herase] at h
              rcases h with ⟨rfl, rfl⟩
              simp [recordAt, hrowk]
          | cons lower tail =>
              have hlower_ne : lower ≠ [] := hnonempty lower (by simp)
              have hlen : 0 < lower.length := List.length_pos_iff_ne_nil.2 hlower_ne
              have hklt : k < lower.entry 0 := by
                have hpair : ColumnStrictTwoRows row lower := columnStrictTwoRows_of_cons_cons hcol
                simpa [hrowk, Row.entry] using hpair 0 hlen
              have hmem0 : lower.entry 0 ∈ lower := by
                rw [Row.entry_eq_getElem lower hlen]
                exact List.getElem_mem hlen
              have hle0 : lower.entry 0 ≤ k := by
                exact hmax _ (List.mem_flatten_of_mem (by simp) hmem0)
              exact False.elim (Nat.not_le_of_lt hklt hle0)
        ·
          simp [unrecordAt, hkrow, herase, hpre] at h
          rcases h with ⟨rfl, rfl⟩
          simp [recordAt, hroweq]
      ·
        have hk_tail : k ∈ rows.flatten := by
          rcases List.mem_flatten.1 hk with ⟨r, hr, hkr⟩
          rcases List.mem_cons.1 hr with rfl | hr
          · exact False.elim (hkrow hkr)
          · exact List.mem_flatten.2 ⟨r, hr, hkr⟩
        have hTtail : IsRSTableau rows := by
          cases rows with
          | nil =>
              simp at hk_tail
          | cons lower tail =>
              exact isRSTableau_tail_of_cons_cons
                ⟨hnonempty, hstrict, hshape, hcol⟩
        have hndtail : EntriesNodup rows := tail_entriesNodup_of_entriesNodup_cons hnd
        have hmaxtail : ∀ x ∈ rows.flatten, x ≤ k := by
          intro x hx
          exact hmax x (by simp [hx])
        cases hrec : unrecordAt k rows with
        | none =>
            simp [unrecordAt, hkrow, hrec] at h
        | some p =>
            rcases p with ⟨j, zs⟩
            simp [unrecordAt, hkrow, hrec] at h
            rcases h with ⟨rfl, rfl⟩
            simpa [recordAt] using
              congrArg (List.cons row)
                (recordAt_of_unrecordAt_max hTtail hndtail hmaxtail hk_tail hrec)

theorem unrecordAt_step_Q {label x : ℕ} {s : State}
    (hnonempty : RowsNonempty s.Q)
    (hlt : EntriesLt label s.Q)
    (hshape : s.P.map List.length = s.Q.map List.length) :
    unrecordAt label (step label x s).Q = some ((insertRows x s.P).newRow, s.Q) := by
  unfold step
  let ins := insertRows x s.P
  have hshapeLen : s.P.length = s.Q.length := by
    simpa using congrArg List.length hshape
  have hnewRow : ins.newRow ≤ s.Q.length := by
    rw [← hshapeLen]
    simpa [ins] using newRow_le_length_insertRows x s.P
  simpa [ins] using unrecordAt_recordAt label ins.newRow s.Q hnonempty hlt hnewRow

theorem unrecordAt_forward_snoc_Q (w : List ℕ) (x : ℕ) :
    unrecordAt (w.length + 1) (forward (w ++ [x])).Q =
      some ((insertRows x (forward w).P).newRow, (forward w).Q) := by
  rw [forward_snoc]
  exact unrecordAt_step_Q
    (hnonempty := rowsNonempty_forward_Q w)
    (hlt := entriesLt_forward_Q w)
    (hshape := shape_forward w)

theorem popCellAt_some_of_rowsNonempty_lt_length :
    ∀ {rows : List Row} {i : ℕ}, RowsNonempty rows → i < rows.length →
      ∃ x rows', popCellAt i rows = some (x, rows')
  | [], i, _, hi => by
      cases hi
  | row :: rows, 0, hnonempty, _ => by
      rcases Row.popLast?_some_of_ne_nil (row := row) (hnonempty row (by simp)) with
        ⟨x, row', hpop⟩
      by_cases hnil : row' = []
      · exact ⟨x, rows, by simp [popCellAt, hpop, hnil]⟩
      · exact ⟨x, row' :: rows, by simp [popCellAt, hpop, hnil]⟩
  | row :: rows, i + 1, hnonempty, hi => by
      have htail : RowsNonempty rows := by
        intro r hr
        exact hnonempty r (by simp [hr])
      have hi' : i < rows.length := Nat.lt_of_succ_lt_succ hi
      rcases popCellAt_some_of_rowsNonempty_lt_length (rows := rows) (i := i) htail hi' with
        ⟨x, rows', hpop⟩
      exact ⟨x, row :: rows', by simp [popCellAt, hpop]⟩

theorem popCellAt_forward_snoc_P_exists (w : List ℕ) (x : ℕ) :
    ∃ y P', popCellAt (insertRows x (forward w).P).newRow (forward (w ++ [x])).P = some (y, P') := by
  rw [forward_snoc]
  unfold step
  have hnonempty : RowsNonempty ((insertRows x (forward w).P).rows) := by
    intro row hrow
    exact rows_nonempty_insertRows x (rowsNonempty_forward_P w) row hrow
  have hlt : (insertRows x (forward w).P).newRow < (insertRows x (forward w).P).rows.length := by
    simpa using newRow_lt_length_insertRows x (forward w).P
  exact popCellAt_some_of_rowsNonempty_lt_length (rows := (insertRows x (forward w).P).rows)
    (i := (insertRows x (forward w).P).newRow) hnonempty hlt

theorem reverseInsertRowsAt_some_mem_head :
    ∀ {row : Row} {rows : List Row} {i : ℕ},
      IsRSTableau (row :: rows) → i < (row :: rows).length →
      ∃ x rows', reverseInsertRowsAt i (row :: rows) = some (x, rows') ∧ x ∈ row
  | row, rows, 0, hT, _ => by
      rcases hT with ⟨hnonempty, _, _, _⟩
      rcases Row.popLast?_some_of_ne_nil (row := row) (hnonempty row (by simp)) with
        ⟨x, row', hpop⟩
      by_cases hnil : row' = []
      · exact ⟨x, rows, by simp [reverseInsertRowsAt, hpop, hnil], Row.popLast?_mem_of_eq_some hpop⟩
      · exact ⟨x, row' :: rows, by simp [reverseInsertRowsAt, hpop, hnil], Row.popLast?_mem_of_eq_some hpop⟩
  | row, [], i + 1, _, hi => by
      simp at hi
  | row, lower :: tail, i + 1, hT, hi => by
      have hTtail : IsRSTableau (lower :: tail) := isRSTableau_tail_of_cons_cons hT
      have hi' : i < (lower :: tail).length := Nat.lt_of_succ_lt_succ hi
      rcases reverseInsertRowsAt_some_mem_head (row := lower) (rows := tail) hTtail hi' with
        ⟨y, rows', hrec, hyrow⟩
      rcases hT with ⟨_, hstrict, hshape, hcol⟩
      have hpair : ColumnStrictTwoRows row lower := columnStrictTwoRows_of_cons_cons hcol
      have hlen : lower.length ≤ row.length := length_head_le_of_shapeSorted_cons_cons hshape
      have hlt : ∃ x ∈ row, x < y := exists_mem_lt_of_columnStrictTwoRows hpair hlen hyrow
      rcases Row.unbump?_some_of_exists_lt (hstrict row (by simp)) hlt with ⟨x, row', hunbump⟩
      exact ⟨x, row' :: rows', by simp [reverseInsertRowsAt, hrec, hunbump],
        Row.unbump?_mem_of_eq_some hunbump⟩

theorem reverseInsertRowsAt_some_of_isRSTableau :
    ∀ {rows : List Row} {i : ℕ},
      IsRSTableau rows → i < rows.length → ∃ x rows', reverseInsertRowsAt i rows = some (x, rows')
  | [], _, _, hi => by
      cases hi
  | row :: rows, i, hT, hi => by
      rcases reverseInsertRowsAt_some_mem_head (row := row) (rows := rows) hT hi with
        ⟨x, rows', hrev, _⟩
      exact ⟨x, rows', hrev⟩

theorem reverseInsertRowsAt_mem_of_eq_some :
    ∀ {rows : List Row} {i x : ℕ} {rows' : List Row},
      reverseInsertRowsAt i rows = some (x, rows') → x ∈ rows.flatten
  | [], 0, _, _, h => by
      simp [reverseInsertRowsAt] at h
  | [], _ + 1, _, _, h => by
      simp [reverseInsertRowsAt] at h
  | row :: rows, 0, x, rows', h => by
      cases hpop : Row.popLast? row with
      | none =>
          simp [reverseInsertRowsAt, hpop] at h
      | some p =>
          rcases p with ⟨y, row''⟩
          by_cases hnil : row'' = []
          · simp [reverseInsertRowsAt, hpop, hnil] at h
            rcases h with ⟨rfl, rfl⟩
            exact List.mem_flatten_of_mem (by simp) (Row.popLast?_mem_of_eq_some hpop)
          · simp [reverseInsertRowsAt, hpop, hnil] at h
            rcases h with ⟨rfl, rfl⟩
            exact List.mem_flatten_of_mem (by simp) (Row.popLast?_mem_of_eq_some hpop)
  | row :: rows, i + 1, x, rows', h => by
      cases hrec : reverseInsertRowsAt i rows with
      | none =>
          simp [reverseInsertRowsAt, hrec] at h
      | some p =>
          rcases p with ⟨y, rows''⟩
          cases hunbump : Row.unbump? y row with
          | none =>
              simp [reverseInsertRowsAt, hrec, hunbump] at h
          | some q =>
              rcases q with ⟨z, row'⟩
              simp [reverseInsertRowsAt, hrec, hunbump] at h
              rcases h with ⟨rfl, rfl⟩
              exact List.mem_flatten_of_mem (by simp) (Row.unbump?_mem_of_eq_some hunbump)

theorem reverseInsertRowsAt_insertRows (x : ℕ) :
    ∀ {rows : List Row},
      RowsStrict rows → RowsNonempty rows → EntriesNodup rows → x ∉ rows.flatten →
      reverseInsertRowsAt (insertRows x rows).newRow (insertRows x rows).rows = some (x, rows)
  | [], _, _, _, _ => by
      simp [reverseInsertRowsAt, insertRows, Row.popLast?]
  | row :: rows, hstrict, hnonempty, hnd, hx => by
      have hxrow : x ∉ row := not_mem_row_of_not_mem_flatten (by simp) hx
      cases hri : Row.insert x row with
      | mk row' bumped =>
          cases bumped with
          | none =>
              have hbump : Row.bump? x row = none := by
                simpa [Row.bumped_insert] using congrArg Row.InsertResult.bumped hri
              have hpop : Row.popLast? row' = some (x, row) := by
                simpa [hri] using Row.popLast?_insert_of_bump_none hbump
              have hrowne : row ≠ [] := hnonempty row (by simp)
              simp [reverseInsertRowsAt, insertRows, hri, hpop, hrowne]
          | some y =>
              have hbump : Row.bump? x row = some y := by
                simpa [Row.bumped_insert] using congrArg Row.InsertResult.bumped hri
              have hyrow : y ∈ row := Row.mem_of_bump?_eq_some hbump
              have hstrict_tail : RowsStrict rows := by
                intro r hr
                exact hstrict r (by simp [hr])
              have hnonempty_tail : RowsNonempty rows := by
                intro r hr
                exact hnonempty r (by simp [hr])
              have hnd_tail : EntriesNodup rows := tail_entriesNodup_of_entriesNodup_cons hnd
              have hytail : y ∉ rows.flatten := not_mem_tail_flatten_of_mem_head hyrow hnd
              have ih :=
                reverseInsertRowsAt_insertRows y hstrict_tail hnonempty_tail hnd_tail hytail
              have hunbump : Row.unbump? y row' = some (x, row) := by
                simpa [hri] using Row.unbump?_insert_of_bump (hstrict row (by simp)) hxrow hbump
              simp [reverseInsertRowsAt, insertRows, hri, ih, hunbump]

theorem insertRows_of_reverseInsertRowsAt_shape :
    ∀ {rows qrows : List Row} {i x : ℕ} {rows' : List Row},
      IsRSTableau rows →
      EntriesNodup rows →
      RowsNonempty qrows →
      rows.map List.length = bumpAt i (qrows.map List.length) →
      reverseInsertRowsAt i rows = some (x, rows') →
      insertRows x rows' = ⟨rows, i⟩
  | [], qrows, 0, x, rows', hT, _, _, hshape, hrev => by
      simp [reverseInsertRowsAt] at hrev
  | [], qrows, i + 1, x, rows', hT, _, _, hshape, hrev => by
      simp [reverseInsertRowsAt] at hrev
  | row :: rows, qrows, 0, x, rows', hT, hnd, hnonemptyQ, hshape, hrev => by
      rcases hT with ⟨hnonempty, hstrict, hshapeRows, hcol⟩
      cases hpop : Row.popLast? row with
      | none =>
          simp [reverseInsertRowsAt, hpop] at hrev
      | some p =>
          rcases p with ⟨y, row₀⟩
          by_cases hnil : row₀ = []
          · simp [reverseInsertRowsAt, hpop, hnil] at hrev
            rcases hrev with ⟨rfl, rfl⟩
            have hrow : row = [y] := by
              simpa [hnil] using Row.eq_append_singleton_of_popLast?_eq_some hpop
            cases qrows with
            | nil =>
                have hrowsnil : rows = [] := by
                  cases rows with
                  | nil => rfl
                  | cons lower tail =>
                      have hshape' : [1, lower.length] = [1] := by
                        simpa [hrow, bumpAt] using hshape
                      simp at hshape'
                subst hrowsnil
                simp [insertRows, hrow]
            | cons qrow qtail =>
                have hqrowne : qrow ≠ [] := hnonemptyQ qrow (by simp)
                have hqrowlen : 0 < qrow.length := List.length_pos_iff_ne_nil.2 hqrowne
                have : False := by
                  have hshape' : 1 = qrow.length + 1 := by
                    simpa [hrow, bumpAt] using congrArg List.head? hshape
                  omega
                exact False.elim this
          · simp [reverseInsertRowsAt, hpop, hnil] at hrev
            rcases hrev with ⟨rfl, rfl⟩
            have hins : Row.insert y row₀ = ⟨row, none⟩ :=
              Row.insert_of_popLast?_eq_some (hstrict row (by simp)) hpop
            rw [insertRows, hins]
  | row :: rows, qrows, i + 1, x, rows', hT, hnd, hnonemptyQ, hshape, hrev => by
      cases rows with
      | nil =>
          cases i <;> simp [reverseInsertRowsAt] at hrev
      | cons lower tail =>
          cases qrows with
          | nil =>
              simp [bumpAt] at hshape
          | cons qrow qtail =>
              rcases hT with ⟨hnonempty, hstrict, hshapeRows, hcol⟩
              have hTtail : IsRSTableau (lower :: tail) :=
                isRSTableau_tail_of_cons_cons ⟨hnonempty, hstrict, hshapeRows, hcol⟩
              have hndtail : EntriesNodup (lower :: tail) :=
                tail_entriesNodup_of_entriesNodup_cons hnd
              have hnonemptyQtail : RowsNonempty qtail := by
                intro r hr
                exact hnonemptyQ r (by simp [hr])
              have hshapeTail : (lower :: tail).map List.length = bumpAt i (qtail.map List.length) := by
                have hshape' :
                    row.length :: (lower :: tail).map List.length =
                      qrow.length :: bumpAt i (qtail.map List.length) := by
                  simpa [bumpAt] using hshape
                exact (List.cons.inj hshape').2
              cases hrec : reverseInsertRowsAt i (lower :: tail) with
              | none =>
                  simp [reverseInsertRowsAt, hrec] at hrev
              | some p =>
                  rcases p with ⟨y, rows₀⟩
                  cases hunbump : Row.unbump? y row with
                  | none =>
                      simp [reverseInsertRowsAt, hrec, hunbump] at hrev
                  | some q =>
                      rcases q with ⟨z, row₀⟩
                      simp [reverseInsertRowsAt, hrec, hunbump] at hrev
                      rcases hrev with ⟨rfl, rfl⟩
                      have hytail : y ∈ (lower :: tail).flatten :=
                        reverseInsertRowsAt_mem_of_eq_some hrec
                      have hyrow : y ∉ row := by
                        intro hyrow
                        exact not_mem_tail_flatten_of_mem_head hyrow hnd hytail
                      have hins : Row.insert z row₀ = ⟨row, some y⟩ := by
                        exact Row.unbump?_insert_of_eq_some (hstrict row (by simp)) hyrow hunbump
                      have ih :
                          insertRows y rows₀ = ⟨lower :: tail, i⟩ :=
                        insertRows_of_reverseInsertRowsAt_shape hTtail hndtail hnonemptyQtail
                          hshapeTail hrec
                      rw [insertRows, hins]
                      simp [ih]

theorem entriesNodup_of_reverseInsertRowsAt_shape
    {rows qrows : List Row} {i x : ℕ} {rows' : List Row}
    (hT : IsRSTableau rows)
    (hnd : EntriesNodup rows)
    (hnonemptyQ : RowsNonempty qrows)
    (hshape : rows.map List.length = bumpAt i (qrows.map List.length))
    (hrev : reverseInsertRowsAt i rows = some (x, rows')) :
    EntriesNodup rows' := by
  have hins : insertRows x rows' = ⟨rows, i⟩ :=
    insertRows_of_reverseInsertRowsAt_shape hT hnd hnonemptyQ hshape hrev
  have hperm : List.Perm rows.flatten (x :: rows'.flatten) := by
    simpa [hins, List.flatten] using (perm_flatten_insertRows x rows')
  exact (List.nodup_cons.1 (hperm.nodup_iff.mp hnd)).2

theorem not_mem_of_reverseInsertRowsAt_shape
    {rows qrows : List Row} {i x : ℕ} {rows' : List Row}
    (hT : IsRSTableau rows)
    (hnd : EntriesNodup rows)
    (hnonemptyQ : RowsNonempty qrows)
    (hshape : rows.map List.length = bumpAt i (qrows.map List.length))
    (hrev : reverseInsertRowsAt i rows = some (x, rows')) :
    x ∉ rows'.flatten := by
  have hins : insertRows x rows' = ⟨rows, i⟩ :=
    insertRows_of_reverseInsertRowsAt_shape hT hnd hnonemptyQ hshape hrev
  have hperm : List.Perm rows.flatten (x :: rows'.flatten) := by
    simpa [hins, List.flatten] using (perm_flatten_insertRows x rows')
  exact (List.nodup_cons.1 (hperm.nodup_iff.mp hnd)).1

theorem reverseInsertRowsAt_rowsStrict :
    ∀ {rows qrows : List Row} {i x : ℕ} {rows' : List Row},
      IsRSTableau rows →
      EntriesNodup rows →
      RowsNonempty qrows →
      rows.map List.length = bumpAt i (qrows.map List.length) →
      reverseInsertRowsAt i rows = some (x, rows') →
      RowsStrict rows'
  | [], qrows, 0, x, rows', hT, _, _, hshape, hrev => by
      simp [reverseInsertRowsAt] at hrev
  | [], qrows, i + 1, x, rows', hT, _, _, hshape, hrev => by
      simp [reverseInsertRowsAt] at hrev
  | row :: rows, qrows, 0, x, rows', hT, hnd, hnonemptyQ, hshape, hrev => by
      rcases hT with ⟨hnonempty, hstrict, hshapeRows, hcol⟩
      cases hpop : Row.popLast? row with
      | none =>
          simp [reverseInsertRowsAt, hpop] at hrev
      | some p =>
          rcases p with ⟨y, row₀⟩
          by_cases hnil : row₀ = []
          · simp [reverseInsertRowsAt, hpop, hnil] at hrev
            rcases hrev with ⟨rfl, rfl⟩
            intro r hr
            exact hstrict r (by simp [hr])
          · simp [reverseInsertRowsAt, hpop, hnil] at hrev
            rcases hrev with ⟨rfl, rfl⟩
            intro r hr
            rcases List.mem_cons.1 hr with rfl | hr
            · exact Row.strict_of_popLast?_eq_some (hstrict row (by simp)) hpop
            · exact hstrict r (by simp [hr])
  | row :: rows, qrows, i + 1, x, rows', hT, hnd, hnonemptyQ, hshape, hrev => by
      cases rows with
      | nil =>
          cases i <;> simp [reverseInsertRowsAt] at hrev
      | cons lower tail =>
          cases qrows with
          | nil =>
              simp [bumpAt] at hshape
          | cons qrow qtail =>
              rcases hT with ⟨hnonempty, hstrict, hshapeRows, hcol⟩
              have hTtail : IsRSTableau (lower :: tail) :=
                isRSTableau_tail_of_cons_cons ⟨hnonempty, hstrict, hshapeRows, hcol⟩
              have hndtail : EntriesNodup (lower :: tail) :=
                tail_entriesNodup_of_entriesNodup_cons hnd
              have hnonemptyQtail : RowsNonempty qtail := by
                intro r hr
                exact hnonemptyQ r (by simp [hr])
              have hshapeTail : (lower :: tail).map List.length = bumpAt i (qtail.map List.length) := by
                have hshape' :
                    row.length :: (lower :: tail).map List.length =
                      qrow.length :: bumpAt i (qtail.map List.length) := by
                  simpa [bumpAt] using hshape
                exact (List.cons.inj hshape').2
              cases hrec : reverseInsertRowsAt i (lower :: tail) with
              | none =>
                  simp [reverseInsertRowsAt, hrec] at hrev
              | some p =>
                  rcases p with ⟨y, rows₀⟩
                  cases hunbump : Row.unbump? y row with
                  | none =>
                      simp [reverseInsertRowsAt, hrec, hunbump] at hrev
                  | some q =>
                      rcases q with ⟨z, row₀⟩
                      simp [reverseInsertRowsAt, hrec, hunbump] at hrev
                      rcases hrev with ⟨rfl, rfl⟩
                      have hytail : y ∈ (lower :: tail).flatten :=
                        reverseInsertRowsAt_mem_of_eq_some hrec
                      have hyrow : y ∉ row := by
                        intro hyrow
                        exact not_mem_tail_flatten_of_mem_head hyrow hnd hytail
                      have hstrict_tail : RowsStrict rows₀ :=
                        reverseInsertRowsAt_rowsStrict hTtail hndtail hnonemptyQtail
                          hshapeTail hrec
                      intro r hr
                      rcases List.mem_cons.1 hr with rfl | hr
                      · exact Row.strict_of_unbump?_eq_some (hstrict row (by simp)) hyrow hunbump
                      · exact hstrict_tail r hr

theorem reverseInsertRowsAt_shape :
    ∀ {rows qrows : List Row} {i x : ℕ} {rows' : List Row},
      RowsNonempty qrows →
      rows.map List.length = bumpAt i (qrows.map List.length) →
      reverseInsertRowsAt i rows = some (x, rows') →
      rows'.map List.length = qrows.map List.length
  | [], qrows, 0, x, rows', hnonemptyQ, hshape, hrev => by
      simp [reverseInsertRowsAt] at hrev
  | [], qrows, i + 1, x, rows', hnonemptyQ, hshape, hrev => by
      simp [reverseInsertRowsAt] at hrev
  | row :: rows, qrows, 0, x, rows', hnonemptyQ, hshape, hrev => by
      cases hpop : Row.popLast? row with
      | none =>
          simp [reverseInsertRowsAt, hpop] at hrev
      | some p =>
          rcases p with ⟨y, row₀⟩
          by_cases hnil : row₀ = []
          · simp [reverseInsertRowsAt, hpop, hnil] at hrev
            rcases hrev with ⟨rfl, rfl⟩
            cases qrows with
            | nil =>
                cases rows with
                | nil =>
                    rfl
                | cons lower tail =>
                    have : False := by
                      simp [bumpAt] at hshape
                    exact False.elim this
            | cons qrow qtail =>
                have : False := by
                  have hqrow : qrow ≠ [] := hnonemptyQ qrow (by simp)
                  have hrow : row = [y] := by
                    simpa [hnil] using Row.eq_append_singleton_of_popLast?_eq_some hpop
                  simp [hrow, bumpAt] at hshape
                  have hqrownil : qrow = [] := by simpa using hshape.1
                  exact hqrow hqrownil
                exact False.elim this
          · simp [reverseInsertRowsAt, hpop, hnil] at hrev
            rcases hrev with ⟨rfl, rfl⟩
            cases qrows with
            | nil =>
                have hrow : row = row₀ ++ [y] := Row.eq_append_singleton_of_popLast?_eq_some hpop
                have : row₀ = [] := by
                  have hshape' : row.length = 1 ∧ rows = [] := by
                    simpa [bumpAt] using hshape
                  have hlen : row.length = 1 := hshape'.1
                  have : row₀.length = 0 := by simpa [hrow] using hlen
                  simpa using this
                exact False.elim (hnil this)
            | cons qrow qtail =>
                have hrow : row = row₀ ++ [y] := Row.eq_append_singleton_of_popLast?_eq_some hpop
                have hshape' :
                    row₀.length = qrow.length ∧ rows.map List.length = qtail.map List.length := by
                  simpa [hrow, hnil, bumpAt] using hshape
                have hlen : row₀.length = qrow.length := by
                  exact hshape'.1
                have htail : rows.map List.length = qtail.map List.length := by
                  exact hshape'.2
                simp [hlen, htail]
  | row :: rows, qrows, i + 1, x, rows', hnonemptyQ, hshape, hrev => by
      cases rows with
      | nil =>
          cases i <;> simp [reverseInsertRowsAt] at hrev
      | cons lower tail =>
          cases qrows with
          | nil =>
              simp [bumpAt] at hshape
          | cons qrow qtail =>
              cases hrec : reverseInsertRowsAt i (lower :: tail) with
              | none =>
                  simp [reverseInsertRowsAt, hrec] at hrev
              | some p =>
                  rcases p with ⟨y, rows₀⟩
                  cases hunbump : Row.unbump? y row with
                  | none =>
                      simp [reverseInsertRowsAt, hrec, hunbump] at hrev
                  | some q =>
                      rcases q with ⟨z, row₀⟩
                      simp [reverseInsertRowsAt, hrec, hunbump] at hrev
                      rcases hrev with ⟨rfl, rfl⟩
                      have hshapeTail : (lower :: tail).map List.length = bumpAt i (qtail.map List.length) := by
                        have hshape' :
                            row.length :: (lower :: tail).map List.length =
                              qrow.length :: bumpAt i (qtail.map List.length) := by
                          simpa [bumpAt] using hshape
                        exact (List.cons.inj hshape').2
                      have ih : rows₀.map List.length = qtail.map List.length :=
                        reverseInsertRowsAt_shape
                          (by
                            intro r hr
                            exact hnonemptyQ r (by simp [hr]))
                          hshapeTail hrec
                      have hrowlen : row₀.length = qrow.length := by
                        have hlenrow : row.length = qrow.length := by
                          exact (List.cons.inj (by simpa [bumpAt] using hshape)).1
                        have hlen' : row₀.length = row.length := by
                          simpa using Row.length_of_unbump?_eq_some hunbump
                        omega
                      simp [hrowlen, ih]

theorem reverseInsertRowsAt_columnStrict :
    ∀ {rows qrows : List Row} {i x : ℕ} {rows' : List Row},
      IsRSTableau rows →
      EntriesNodup rows →
      IsRSTableau qrows →
      rows.map List.length = bumpAt i (qrows.map List.length) →
      reverseInsertRowsAt i rows = some (x, rows') →
      ColumnStrict rows'
  | [], qrows, 0, x, rows', hT, _, hTQ, hshape, hrev => by
      simp [reverseInsertRowsAt] at hrev
  | [], qrows, i + 1, x, rows', hT, _, hTQ, hshape, hrev => by
      simp [reverseInsertRowsAt] at hrev
  | row :: rows, qrows, 0, x, rows', hT, hnd, hTQ, hshape, hrev => by
      rcases hT with ⟨hnonempty, hstrict, hshapeRows, hcol⟩
      cases hpop : Row.popLast? row with
      | none =>
          simp [reverseInsertRowsAt, hpop] at hrev
      | some p =>
          rcases p with ⟨y, row₀⟩
          by_cases hnil : row₀ = []
          ·
            simp [reverseInsertRowsAt, hpop, hnil] at hrev
            rcases hrev with ⟨rfl, rfl⟩
            cases rows with
            | nil =>
                simpa using columnStrict_nil
            | cons lower tail =>
                simpa using
                  (columnStrict_cons_cons_iff (upper := row) (lower := lower) (rows := tail)).1 hcol |>.2
          ·
            simp [reverseInsertRowsAt, hpop, hnil] at hrev
            rcases hrev with ⟨rfl, rfl⟩
            cases rows with
            | nil =>
                simpa using columnStrict_singleton row₀
            | cons lower tail =>
                have hshape' : (row₀ :: lower :: tail).map List.length = qrows.map List.length := by
                  apply reverseInsertRowsAt_shape (x := y) hTQ.1 hshape
                  simp [reverseInsertRowsAt, hpop, hnil]
                have hlen0 : lower.length ≤ row₀.length := by
                  cases qrows with
                  | nil =>
                      simp at hshape'
                  | cons qrow qtail =>
                      cases qtail with
                      | nil =>
                          have : False := by
                            have hlen := congrArg List.length hshape'
                            simp at hlen
                          exact False.elim this
                      | cons qlower qtail' =>
                          have hshapeQ' : ShapeSorted (qrow :: qlower :: qtail') := by
                            simpa using hTQ.2.2.1
                          have hq : qlower.length ≤ qrow.length :=
                            length_head_le_of_shapeSorted_cons_cons hshapeQ'
                          have hhead : row₀.length = qrow.length := (List.cons.inj hshape').1
                          have htail' : lower.length :: tail.map List.length = qlower.length :: qtail'.map List.length :=
                            (List.cons.inj hshape').2
                          have hsecond : lower.length = qlower.length := (List.cons.inj htail').1
                          omega
                apply (columnStrict_cons_cons_iff (upper := row₀) (lower := lower) (rows := tail)).2
                refine ⟨?_, ?_⟩
                ·
                  exact columnStrictTwoRows_of_popLast_upper
                    (columnStrictTwoRows_of_cons_cons hcol) hlen0 hpop
                ·
                  exact (columnStrict_cons_cons_iff (upper := row) (lower := lower) (rows := tail)).1 hcol |>.2
  | row :: rows, qrows, i + 1, x, rows', hT, hnd, hTQ, hshape, hrev => by
      cases rows with
      | nil =>
          cases i <;> simp [reverseInsertRowsAt] at hrev
      | cons lower tail =>
          cases qrows with
          | nil =>
              simp [bumpAt] at hshape
          | cons qrow qtail =>
              rcases hT with ⟨hnonempty, hstrict, hshapeRows, hcol⟩
              rcases hTQ with ⟨hnonemptyQ, hstrictQ, hshapeQ, hcolQ⟩
              have hTtail : IsRSTableau (lower :: tail) :=
                isRSTableau_tail_of_cons_cons ⟨hnonempty, hstrict, hshapeRows, hcol⟩
              have hndtail : EntriesNodup (lower :: tail) :=
                tail_entriesNodup_of_entriesNodup_cons hnd
              have hTQtail : IsRSTableau qtail := by
                refine ⟨?_, ?_, shapeSorted_tail_of_cons hshapeQ, columnStrict_tail_of_cons hcolQ⟩
                ·
                  intro r hr
                  exact hnonemptyQ r (by simp [hr])
                ·
                  intro r hr
                  exact hstrictQ r (by simp [hr])
              have hshapeTail : (lower :: tail).map List.length = bumpAt i (qtail.map List.length) := by
                have hshape' :
                    row.length :: (lower :: tail).map List.length =
                      qrow.length :: bumpAt i (qtail.map List.length) := by
                  simpa [bumpAt] using hshape
                exact (List.cons.inj hshape').2
              cases hrec : reverseInsertRowsAt i (lower :: tail) with
              | none =>
                  simp [reverseInsertRowsAt, hrec] at hrev
              | some p =>
                  rcases p with ⟨y, rows₀⟩
                  cases hunbump : Row.unbump? y row with
                  | none =>
                      simp [reverseInsertRowsAt, hrec, hunbump] at hrev
                  | some q =>
                      rcases q with ⟨z, row₀⟩
                      simp [reverseInsertRowsAt, hrec, hunbump] at hrev
                      rcases hrev with ⟨rfl, rfl⟩
                      have hcolTail : ColumnStrict rows₀ :=
                        reverseInsertRowsAt_columnStrict hTtail hndtail hTQtail hshapeTail hrec
                      have hytail : y ∈ (lower :: tail).flatten :=
                        reverseInsertRowsAt_mem_of_eq_some hrec
                      have hyrow : y ∉ row := by
                        intro hyrow
                        exact not_mem_tail_flatten_of_mem_head hyrow hnd hytail
                      cases rows₀ with
                      | nil =>
                          simpa using columnStrict_singleton row₀
                      | cons lower₀ tail₀ =>
                          apply (columnStrict_cons_cons_iff
                            (upper := row₀) (lower := lower₀) (rows := tail₀)).2
                          refine ⟨?_, hcolTail⟩
                          cases i with
                          | zero =>
                              cases hpopLower : Row.popLast? lower with
                              | none =>
                                  simp [reverseInsertRowsAt, hpopLower] at hrec
                              | some pLower =>
                                  rcases pLower with ⟨y', lower'⟩
                                  by_cases hnilLower : lower' = []
                                  ·
                                      simp [reverseInsertRowsAt, hpopLower, hnilLower] at hrec
                                      rcases hrec with ⟨hyEq, hrowsEq⟩
                                      subst hyEq
                                      have hlowerSingle : lower = [y'] := by
                                        have hEq := Row.eq_append_singleton_of_popLast?_eq_some hpopLower
                                        simpa [hnilLower] using hEq
                                      cases tail with
                                      | nil =>
                                          simp at hrowsEq
                                      | cons next tail' =>
                                          simp at hrowsEq
                                          rcases hrowsEq with ⟨rfl, rfl⟩
                                          have hcolLowerTail : ColumnStrict (lower :: next :: tail') := by
                                            simpa using
                                              (columnStrict_cons_cons_iff
                                                (upper := row) (lower := lower) (rows := next :: tail')).1 hcol |>.2
                                          have hcolTailOrig : ColumnStrict ([y'] :: next :: tail') := by
                                            simpa [hlowerSingle] using hcolLowerTail
                                          have hpairLowerNext : ColumnStrictTwoRows [y'] next :=
                                            columnStrictTwoRows_of_cons_cons hcolTailOrig
                                          have hlenNext : next.length ≤ 1 := by
                                            have hshapeLowerTail : ShapeSorted (lower :: next :: tail') := by
                                              simpa using shapeSorted_tail_of_cons hshapeRows
                                            have hshapeSub : ShapeSorted ([y'] :: next :: tail') := by
                                              simpa [hlowerSingle] using hshapeLowerTail
                                            simpa using length_head_le_of_shapeSorted_cons_cons hshapeSub
                                          exact columnStrictTwoRows_of_unbump_upper_singleton_lower
                                            (by simpa [hlowerSingle] using columnStrictTwoRows_of_cons_cons hcol)
                                            hpairLowerNext
                                            (hstrict row (by simp))
                                            hyrow
                                            hunbump
                                            hlenNext
                                  ·
                                      simp [reverseInsertRowsAt, hpopLower, hnilLower] at hrec
                                      rcases hrec with ⟨hyEq, hrowsEq⟩
                                      subst hyEq
                                      rcases hrowsEq with ⟨rfl, rfl⟩
                                      exact columnStrictTwoRows_of_unbump_upper_popLast_lower
                                        (columnStrictTwoRows_of_cons_cons hcol)
                                        (length_head_le_of_shapeSorted_cons_cons hshapeRows)
                                        (hstrict row (by simp))
                                        (hstrict lower (by simp))
                                        hyrow
                                        hunbump
                                        hpopLower
                          | succ i' =>
                              cases tail with
                              | nil =>
                                  cases i' <;> simp [reverseInsertRowsAt] at hrec
                              | cons next tail' =>
                                  cases hrec' : reverseInsertRowsAt i' (next :: tail') with
                                  | none =>
                                      simp [reverseInsertRowsAt, hrec'] at hrec
                                  | some pTail =>
                                      rcases pTail with ⟨w, tailRows⟩
                                      cases hunbumpLower : Row.unbump? w lower with
                                      | none =>
                                          simp [reverseInsertRowsAt, hrec', hunbumpLower] at hrec
                                      | some qLower =>
                                          rcases qLower with ⟨y', lower'⟩
                                          simp [reverseInsertRowsAt, hrec', hunbumpLower] at hrec
                                          rcases hrec with ⟨hyEq, hrowsEq⟩
                                          subst hyEq
                                          rcases hrowsEq with ⟨rfl, rfl⟩
                                          have hzlower : w ∉ lower := by
                                            intro hwlower
                                            exact not_mem_tail_flatten_of_mem_head hwlower hndtail
                                              (reverseInsertRowsAt_mem_of_eq_some hrec')
                                          exact columnStrictTwoRows_of_unbump_upper_unbump_lower
                                            (columnStrictTwoRows_of_cons_cons hcol)
                                            (length_head_le_of_shapeSorted_cons_cons hshapeRows)
                                            (hstrict row (by simp))
                                            (hstrict lower (by simp))
                                            hyrow
                                            hzlower
                                            hunbump
                                            hunbumpLower

theorem reverseInsertRowsAt_forward_snoc_P {w : List ℕ} {x : ℕ}
    (hnd : (w ++ [x]).Nodup) :
    reverseInsertRowsAt (insertRows x (forward w).P).newRow (forward (w ++ [x])).P =
      some (x, (forward w).P) := by
  rw [forward_snoc]
  unfold step
  have hwnd : w.Nodup := (List.nodup_append.1 hnd).1
  apply reverseInsertRowsAt_insertRows
  · exact rowsStrict_forward_P hwnd
  · exact rowsNonempty_forward_P w
  · exact entriesNodup_forward_P hwnd
  ·
    have hnot : x ∉ w := by
      intro hxw
      exact ((List.nodup_append.1 hnd).2.2 x hxw x (by simp)) rfl
    intro hxP
    have hxwrev : x ∈ w.reverse := (perm_flatten_forward_P w).subset hxP
    exact hnot ((List.mem_reverse).1 hxwrev)

/-- One backward RS step at recording label `label`. -/
def stepBack (label : ℕ) (s : State) : Option (ℕ × State) :=
  match unrecordAt label s.Q with
  | none => none
  | some (i, Q') =>
      match reverseInsertRowsAt i s.P with
      | none => none
      | some (x, P') => some (x, ⟨P', Q'⟩)

theorem stepBack_forward_snoc {w : List ℕ} {x : ℕ}
    (hnd : (w ++ [x]).Nodup) :
    stepBack (w.length + 1) (forward (w ++ [x])) = some (x, forward w) := by
  unfold stepBack
  rw [unrecordAt_forward_snoc_Q w x]
  simp [reverseInsertRowsAt_forward_snoc_P hnd]

/-- First half of a backward RS step: remove the last recording box, keeping `P` unchanged and
remembering the row where the corner was removed. -/
def removeLastBox (label : ℕ) (s : State) : Option (ℕ × State) :=
  match unrecordAt label s.Q with
  | none => none
  | some (i, Q') => some (i, ⟨s.P, Q'⟩)

theorem removeLastBox_eq_some {label : ℕ} {s s0 : State} {r : ℕ}
    (h : removeLastBox label s = some (r, s0)) :
    s0.P = s.P ∧ unrecordAt label s.Q = some (r, s0.Q) := by
  unfold removeLastBox at h
  cases hunrec : unrecordAt label s.Q with
  | none =>
      simp [hunrec] at h
  | some p =>
      rcases p with ⟨i, Q'⟩
      simp [hunrec] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, by simpa using hunrec⟩

/-- Iterate backward RS for `n` recording labels, recovering a word when successful. -/
def backwardAux : ℕ → State → Option (List ℕ)
  | 0, s =>
      if _hs : s.P = [] ∧ s.Q = [] then
        some []
      else
        none
  | n + 1, s =>
      match stepBack (n + 1) s with
      | none => none
      | some (x, s') =>
          match backwardAux n s' with
          | none => none
          | some xs => some (xs ++ [x])

/-- Backward RS, using the cell count of `P` as the number of steps to unwind. -/
def backward (s : State) : Option (List ℕ) :=
  backwardAux (cellCount s.P) s

theorem backwardAux_forward {w : List ℕ} (hnd : w.Nodup) :
    backwardAux w.length (forward w) = some w := by
  induction w using List.reverseRecOn with
  | nil =>
      simp [backwardAux, forward, forwardAux]
  | append_singleton w x ih =>
      have hwnd : w.Nodup := (List.nodup_append.1 hnd).1
      simp [backwardAux, stepBack_forward_snoc hnd, ih hwnd]

theorem backward_forward {w : List ℕ} (hnd : w.Nodup) :
    backward (forward w) = some w := by
  simpa [backward, cellCount_forward_P] using backwardAux_forward hnd

/-- Concrete standard RS pairs of size `n`: both tableaux are RS tableaux, have the same shape,
and both contain exactly the labels `1, …, n`. -/
def IsStandardState (n : ℕ) (s : State) : Prop :=
  IsRSTableau s.P ∧
  EntriesNodup s.P ∧
  IsRSTableau s.Q ∧
  EntriesNodup s.Q ∧
  s.P.map List.length = s.Q.map List.length ∧
  List.Perm s.P.flatten (revLabelsFrom 1 n) ∧
  List.Perm s.Q.flatten (revLabelsFrom 1 n)

theorem mem_revLabelsFrom_last (label len : ℕ) :
    label + len ∈ revLabelsFrom label (len + 1) := by
  induction len generalizing label with
  | zero =>
      simp [revLabelsFrom]
  | succ len ih =>
      have hmem : (label + 1) + len ∈ revLabelsFrom (label + 1) (len + 1) := ih (label + 1)
      rw [revLabelsFrom]
      exact List.mem_append.2 <| Or.inl <| by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmem

theorem revLabelsFrom_succ (label len : ℕ) :
    revLabelsFrom label (len + 1) = (label + len) :: revLabelsFrom label len := by
  induction len generalizing label with
  | zero =>
      simp [revLabelsFrom]
  | succ len ih =>
      rw [revLabelsFrom, ih (label + 1)]
      simp [revLabelsFrom, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem length_revLabelsFrom (label len : ℕ) :
    (revLabelsFrom label len).length = len := by
  induction len generalizing label with
  | zero =>
      simp [revLabelsFrom]
  | succ len ih =>
      simp [revLabelsFrom, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Reverse-direction invariant: `Q` is a standard recording tableau of size `n`, while `P` is an
RS tableau of the same shape with distinct entries. This is the induction target that survives a
single backward step; unlike `IsStandardState`, it does not constrain the specific label set in
`P`. -/
def IsBackwardState (n : ℕ) (s : State) : Prop :=
  IsRSTableau s.P ∧
  EntriesNodup s.P ∧
  IsRSTableau s.Q ∧
  EntriesNodup s.Q ∧
  s.P.map List.length = s.Q.map List.length ∧
  List.Perm s.Q.flatten (revLabelsFrom 1 n)

/-- Intermediate reverse-direction state after removing the label `n + 1` from `Q` but before
running reverse insertion on `P`. `P` still has one extra cell, and `r` records the row where that
cell lives. -/
def IsPartialBackwardState (n r : ℕ) (s : State) : Prop :=
  IsRSTableau s.P ∧
  EntriesNodup s.P ∧
  IsRSTableau s.Q ∧
  EntriesNodup s.Q ∧
  s.P.map List.length = bumpAt r (s.Q.map List.length) ∧
  List.Perm s.Q.flatten (revLabelsFrom 1 n)

theorem forward_isBackwardState {w : List ℕ} (hnd : w.Nodup) :
    IsBackwardState w.length (forward w) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isRSTableau_forward_P hnd
  · exact entriesNodup_forward_P hnd
  · exact isRSTableau_forward_Q hnd
  · exact entriesNodup_forward_Q w
  · exact shape_forward w
  · exact perm_flatten_forward_Q w

/-- The first backward step exists for any state satisfying the reverse-direction invariant. -/
theorem stepBack_some_of_backwardState {n : ℕ} {s : State}
    (hstate : IsBackwardState (n + 1) s) :
    ∃ x s', stepBack (n + 1) s = some (x, s') := by
  rcases hstate with ⟨hTP, hndP, hTQ, hndQ, hshape, hpermQ⟩
  have hkQ : n + 1 ∈ s.Q.flatten := by
    have hmem : n + 1 ∈ revLabelsFrom 1 (n + 1) := by
      simpa [Nat.add_comm] using mem_revLabelsFrom_last 1 n
    exact hpermQ.symm.subset hmem
  rcases unrecordAt_some_of_mem_flatten hkQ with ⟨i, Q', hQ⟩
  have hiQ : i < s.Q.length := unrecordAt_index_lt_length hQ
  have hlen : s.P.length = s.Q.length := by
    simpa using congrArg List.length hshape
  have hiP : i < s.P.length := by
    rw [hlen]
    exact hiQ
  rcases reverseInsertRowsAt_some_of_isRSTableau hTP hiP with ⟨x, P', hP⟩
  exact ⟨x, ⟨P', Q'⟩, by simp [stepBack, hQ, hP]⟩

theorem removeLastBox_spec {n : ℕ} {s : State}
    (hstate : IsBackwardState (n + 1) s) :
    ∃ r s0,
      removeLastBox (n + 1) s = some (r, s0) ∧
      IsPartialBackwardState n r s0 ∧
      recordAt (n + 1) r s0.Q = s.Q := by
  rcases hstate with ⟨hTP, hndP, hTQ, hndQ, hshape, hpermQ⟩
  have hk : n + 1 ∈ s.Q.flatten := by
    have hmem : n + 1 ∈ revLabelsFrom 1 (n + 1) := by
      simpa [Nat.add_comm] using mem_revLabelsFrom_last 1 n
    exact hpermQ.symm.subset hmem
  have hmax : ∀ x ∈ s.Q.flatten, x ≤ n + 1 := by
    intro x hx
    have hx' : x ∈ revLabelsFrom 1 (n + 1) := hpermQ.subset hx
    have hlt : x < 1 + (n + 1) := lt_add_of_mem_revLabelsFrom hx'
    omega
  rcases unrecordAt_some_of_mem_flatten hk with ⟨r, Q', hunrec⟩
  have hrecord : recordAt (n + 1) r Q' = s.Q :=
    recordAt_of_unrecordAt_max hTQ hndQ hmax hk hunrec
  have hi : r ≤ Q'.length := unrecordAt_index_le_length_result hunrec
  have hflat : List.Perm s.Q.flatten ((n + 1) :: Q'.flatten) := by
    simpa [hrecord, List.flatten] using perm_flatten_recordAt (n + 1) r Q' hi
  have hpermQ' : List.Perm Q'.flatten (revLabelsFrom 1 n) := by
    have hperm' : List.Perm ((n + 1) :: Q'.flatten) (revLabelsFrom 1 (n + 1)) := by
      exact hflat.symm.trans hpermQ
    rw [revLabelsFrom_succ] at hperm'
    have hperm'' : List.Perm ((n + 1) :: Q'.flatten) ((n + 1) :: revLabelsFrom 1 n) := by
      simpa [Nat.add_comm] using hperm'
    exact List.Perm.cons_inv hperm''
  have hTQ' : IsRSTableau Q' := by
    have hTrecord : IsRSTableau (recordAt (n + 1) r Q') := by
      simpa [hrecord] using hTQ
    have hltQ' : EntriesLt (n + 1) Q' := by
      intro row hrow x hx
      have hx' : x ∈ Q'.flatten := List.mem_flatten_of_mem hrow hx
      have hx'' : x ∈ revLabelsFrom 1 n := hpermQ'.subset hx'
      have hltx : x < 1 + n := lt_add_of_mem_revLabelsFrom hx''
      omega
    exact isRSTableau_of_recordAt
      (rowsNonempty_of_unrecordAt hTQ.1 hunrec)
      hltQ'
      hTrecord
  have hndQ' : EntriesNodup Q' := by
    have hnodupCons : ((n + 1) :: Q'.flatten).Nodup := hflat.nodup_iff.mp hndQ
    exact (List.nodup_cons.1 hnodupCons).2
  refine ⟨r, ⟨s.P, Q'⟩, ?_, ?_, hrecord⟩
  · simp [removeLastBox, hunrec]
  · refine ⟨hTP, hndP, hTQ', hndQ', ?_, hpermQ'⟩
    · calc
        s.P.map List.length = s.Q.map List.length := hshape
        _ = (recordAt (n + 1) r Q').map List.length := by rw [hrecord]
        _ = bumpAt r (Q'.map List.length) := shape_recordAt (n + 1) r Q'

theorem stepBack_reconstruct {n : ℕ} {s s' : State} {x : ℕ}
    (hstate : IsBackwardState (n + 1) s)
    (hback : stepBack (n + 1) s = some (x, s')) :
    step (n + 1) x s' = s := by
  rcases removeLastBox_spec hstate with ⟨r, s0, hremove, hpartial, hrecord⟩
  rcases hpartial with ⟨hTP, hndP, hTQ, _, hshape, _⟩
  rcases removeLastBox_eq_some hremove with ⟨hP, hunrec⟩
  rw [hP] at hTP hndP hshape
  unfold stepBack at hback
  rw [hunrec] at hback
  cases hrev : reverseInsertRowsAt r s.P with
  | none =>
      simp [hrev] at hback
  | some q =>
      rcases q with ⟨y, P'⟩
      simp [hrev] at hback
      rcases hback with ⟨rfl, rfl⟩
      have hins : insertRows y P' = ⟨s.P, r⟩ :=
        insertRows_of_reverseInsertRowsAt_shape hTP hndP hTQ.1 hshape hrev
      unfold step
      simp [hins, hrecord]

theorem stepBack_preserves_except_column {n : ℕ} {s s' : State} {x : ℕ}
    (hstate : IsBackwardState (n + 1) s)
    (hback : stepBack (n + 1) s = some (x, s')) :
    RowsStrict s'.P ∧
    EntriesNodup s'.P ∧
    IsRSTableau s'.Q ∧
    EntriesNodup s'.Q ∧
    s'.P.map List.length = s'.Q.map List.length ∧
    List.Perm s'.Q.flatten (revLabelsFrom 1 n) := by
  rcases removeLastBox_spec hstate with ⟨r, s0, hremove, hpartial, _⟩
  rcases hpartial with ⟨hTP, hndP, hTQ, hndQ, hshape, hpermQ⟩
  rcases removeLastBox_eq_some hremove with ⟨hP, hunrec⟩
  rw [hP] at hTP hndP hshape
  unfold stepBack at hback
  rw [hunrec] at hback
  cases hrev : reverseInsertRowsAt r s.P with
  | none =>
      simp [hrev] at hback
  | some q =>
      rcases q with ⟨y, P'⟩
      simp [hrev] at hback
      rcases hback with ⟨rfl, rfl⟩
      have hrowsP' : RowsStrict P' :=
        reverseInsertRowsAt_rowsStrict hTP hndP hTQ.1 hshape hrev
      have hndP' : EntriesNodup P' :=
        entriesNodup_of_reverseInsertRowsAt_shape hTP hndP hTQ.1 hshape hrev
      have hshapeP' : P'.map List.length = s0.Q.map List.length :=
        reverseInsertRowsAt_shape hTQ.1 hshape hrev
      exact ⟨hrowsP', hndP', hTQ, hndQ, hshapeP', hpermQ⟩

theorem rowsNonempty_of_shape_eq_of_rowsNonempty {rows qrows : List Row}
    (hshape : rows.map List.length = qrows.map List.length)
    (hnonemptyQ : RowsNonempty qrows) :
    RowsNonempty rows := by
  intro row hrow hnil
  have hmemLen : row.length ∈ rows.map List.length := List.mem_map.2 ⟨row, hrow, rfl⟩
  rw [hshape] at hmemLen
  rw [hnil] at hmemLen
  rcases List.mem_map.1 hmemLen with ⟨qrow, hqrow, hlen⟩
  have hqnil : qrow = [] := by
    cases qrow with
    | nil =>
        rfl
    | cons x xs =>
        simp at hlen
  exact hnonemptyQ qrow hqrow hqnil

theorem stepBack_fresh {n : ℕ} {s s' : State} {x : ℕ}
    (hstate : IsBackwardState (n + 1) s)
    (hback : stepBack (n + 1) s = some (x, s')) :
    x ∉ s'.P.flatten := by
  rcases removeLastBox_spec hstate with ⟨r, s0, hremove, hpartial, _⟩
  rcases hpartial with ⟨hTP, hndP, hTQ, _, hshape, _⟩
  rcases removeLastBox_eq_some hremove with ⟨hP, hunrec⟩
  rw [hP] at hTP hndP hshape
  unfold stepBack at hback
  rw [hunrec] at hback
  cases hrev : reverseInsertRowsAt r s.P with
  | none =>
      simp [hrev] at hback
  | some q =>
      rcases q with ⟨y, P'⟩
      simp [hrev] at hback
      rcases hback with ⟨rfl, rfl⟩
      exact not_mem_of_reverseInsertRowsAt_shape hTP hndP hTQ.1 hshape hrev

theorem stepBack_preserves {n : ℕ} {s s' : State} {x : ℕ}
    (hstate : IsBackwardState (n + 1) s)
    (hback : stepBack (n + 1) s = some (x, s')) :
    IsBackwardState n s' := by
  rcases stepBack_preserves_except_column hstate hback with
    ⟨hrowsP', hndP', hTQ', hndQ', hshapeP', hpermQ'⟩
  rcases removeLastBox_spec hstate with ⟨r, s0, hremove, hpartial, _⟩
  rcases hpartial with ⟨hTP, hndP, _, _, hshape, _⟩
  rcases removeLastBox_eq_some hremove with ⟨hP, hunrec⟩
  rw [hP] at hTP hndP hshape
  unfold stepBack at hback
  rw [hunrec] at hback
  cases hrev : reverseInsertRowsAt r s.P with
  | none =>
      simp [hrev] at hback
  | some q =>
      rcases q with ⟨y, P'⟩
      simp [hrev] at hback
      rcases hback with ⟨rfl, rfl⟩
      have hcolP' : ColumnStrict P' :=
        reverseInsertRowsAt_columnStrict hTP hndP hTQ' hshape hrev
      have hnonemptyP' : RowsNonempty P' :=
        rowsNonempty_of_shape_eq_of_rowsNonempty
          (rows := P') (qrows := s0.Q)
          (by simpa using hshapeP') hTQ'.1
      have hshapeSortedP' : ShapeSorted P' := by
        have hshapeSortedQ' : ShapeSorted s0.Q := hTQ'.2.2.1
        unfold ShapeSorted at hshapeSortedQ' ⊢
        simpa [hshapeP'] using hshapeSortedQ'
      refine ⟨?_, hndP', hTQ', hndQ', hshapeP', hpermQ'⟩
      exact ⟨hnonemptyP', hrowsP', hshapeSortedP', hcolP'⟩

theorem rows_eq_nil_of_rowsNonempty_flatten_eq_nil {rows : List Row}
    (hnonempty : RowsNonempty rows)
    (hflat : rows.flatten = []) :
    rows = [] := by
  cases rows with
  | nil =>
      rfl
  | cons row tail =>
      exfalso
      have hrowne : row ≠ [] := hnonempty row (by simp)
      cases row with
      | nil =>
          exact hrowne rfl
      | cons x xs =>
          simp [List.flatten] at hflat

theorem backwardAux_spec_of_backwardState {n : ℕ} {s : State}
    (hstate : IsBackwardState n s) :
    ∃ w, backwardAux n s = some w ∧ w.Nodup ∧ w.length = n ∧ forward w = s := by
  induction n generalizing s with
  | zero =>
      rcases hstate with ⟨hTP, _, hTQ, _, hshape, hpermQ⟩
      have hQnil : s.Q = [] := by
        apply rows_eq_nil_of_rowsNonempty_flatten_eq_nil hTQ.1
        simpa [revLabelsFrom] using hpermQ
      have hPnil : s.P = [] := by
        cases hP : s.P with
        | nil =>
            rfl
        | cons row rows =>
            have hshape' : (row :: rows).map List.length = ([] : List Row).map List.length := by
              simpa [hP, hQnil] using hshape
            simp at hshape'
      refine ⟨[], ?_, by simp, rfl, ?_⟩
      · simp [backwardAux, hPnil, hQnil]
      · cases s
        simp [forward, forwardAux] at hPnil hQnil ⊢
        simp [hPnil, hQnil]
  | succ n ih =>
      rcases stepBack_some_of_backwardState hstate with ⟨x, s', hback⟩
      have hstate' : IsBackwardState n s' := stepBack_preserves hstate hback
      rcases ih hstate' with ⟨w, hbw, hwnd, hwlen, hforw⟩
      have hfresh : x ∉ s'.P.flatten := stepBack_fresh hstate hback
      have hxw : x ∉ w := by
        intro hxw
        have hxwrev : x ∈ w.reverse := (List.mem_reverse).2 hxw
        have hpermP : List.Perm s'.P.flatten w.reverse := by
          simpa [hforw] using perm_flatten_forward_P w
        exact hfresh (hpermP.symm.subset hxwrev)
      refine ⟨w ++ [x], ?_, ?_, by simp [hwlen], ?_⟩
      · simp [backwardAux, hback, hbw]
      ·
        show (w ++ [x]).Nodup
        simpa using hwnd.concat hxw
      · calc
          forward (w ++ [x]) = step (w.length + 1) x (forward w) := forward_snoc w x
          _ = step (n + 1) x s' := by simpa [hwlen, hforw]
          _ = s := stepBack_reconstruct hstate hback

theorem backwardAux_spec_of_standardState {n : ℕ} {s : State}
    (hstd : IsStandardState n s) :
    ∃ w, backwardAux n s = some w ∧ List.Perm w (revLabelsFrom 1 n) ∧ forward w = s := by
  have hback :
      IsBackwardState n s :=
    ⟨hstd.1, hstd.2.1, hstd.2.2.1, hstd.2.2.2.1, hstd.2.2.2.2.1, hstd.2.2.2.2.2.2⟩
  rcases backwardAux_spec_of_backwardState hback with ⟨w, hbw, hwnd, hwlen, hforw⟩
  have hpermP : List.Perm s.P.flatten (revLabelsFrom 1 n) := hstd.2.2.2.2.2.1
  have hpermFw : List.Perm s.P.flatten w.reverse := by
    simpa [hforw] using perm_flatten_forward_P w
  have hpermWrev : List.Perm w.reverse (revLabelsFrom 1 n) := hpermFw.symm.trans hpermP
  have hpermW : List.Perm w (revLabelsFrom 1 n) := w.reverse_perm.symm.trans hpermWrev
  exact ⟨w, hbw, hpermW, hforw⟩

noncomputable def backwardStandardWord (n : ℕ) (s : State) (hs : IsStandardState n s) : List ℕ :=
  Classical.choose (backwardAux_spec_of_standardState hs)

theorem backwardStandardWord_spec {n : ℕ} {s : State} (hs : IsStandardState n s) :
    backwardAux n s = some (backwardStandardWord n s hs) ∧
    List.Perm (backwardStandardWord n s hs) (revLabelsFrom 1 n) ∧
    forward (backwardStandardWord n s hs) = s := by
  exact Classical.choose_spec (backwardAux_spec_of_standardState hs)

theorem forward_isStandardState {n : ℕ} {w : List ℕ}
    (hw : List.Perm w (revLabelsFrom 1 n)) :
    IsStandardState n (forward w) := by
  have hlen : w.length = n := by
    simpa [length_revLabelsFrom] using hw.length_eq
  have hw' : List.Perm w (revLabelsFrom 1 w.length) := by
    simpa [hlen] using hw
  simpa [IsStandardState, hlen] using forward_perm_rs_spec hw'

theorem stepBack_some_of_standardState {n : ℕ} {s : State}
    (hstd : IsStandardState (n + 1) s) :
    ∃ x s', stepBack (n + 1) s = some (x, s') := by
  exact stepBack_some_of_backwardState
    ⟨hstd.1, hstd.2.1, hstd.2.2.1, hstd.2.2.2.1, hstd.2.2.2.2.1, hstd.2.2.2.2.2.2⟩

theorem unrecordAt_standard_Q {n : ℕ} {rows : List Row}
    (hT : IsRSTableau rows)
    (hnd : EntriesNodup rows)
    (hperm : List.Perm rows.flatten (revLabelsFrom 1 (n + 1))) :
    ∃ i rows',
      unrecordAt (n + 1) rows = some (i, rows') ∧
      recordAt (n + 1) i rows' = rows ∧
      IsRSTableau rows' ∧
      EntriesNodup rows' ∧
      List.Perm rows'.flatten (revLabelsFrom 1 n) := by
  have hk : n + 1 ∈ rows.flatten := by
    have hmem : n + 1 ∈ revLabelsFrom 1 (n + 1) := by
      simpa [Nat.add_comm] using mem_revLabelsFrom_last 1 n
    exact hperm.symm.subset hmem
  have hmax : ∀ x ∈ rows.flatten, x ≤ n + 1 := by
    intro x hx
    have hx' : x ∈ revLabelsFrom 1 (n + 1) := hperm.subset hx
    have hlt : x < 1 + (n + 1) := lt_add_of_mem_revLabelsFrom hx'
    omega
  rcases unrecordAt_some_of_mem_flatten hk with ⟨i, rows', hrec⟩
  have hrecord : recordAt (n + 1) i rows' = rows :=
    recordAt_of_unrecordAt_max hT hnd hmax hk hrec
  have hi : i ≤ rows'.length := unrecordAt_index_le_length_result hrec
  have hflat : List.Perm rows.flatten ((n + 1) :: rows'.flatten) := by
    simpa [hrecord, List.flatten] using perm_flatten_recordAt (n + 1) i rows' hi
  have hnd' : EntriesNodup rows' := by
    have hnodupCons : ((n + 1) :: rows'.flatten).Nodup := hflat.nodup_iff.mp hnd
    exact (List.nodup_cons.1 hnodupCons).2
  have hperm' : List.Perm ((n + 1) :: rows'.flatten) (revLabelsFrom 1 (n + 1)) := by
    exact hflat.symm.trans hperm
  have htail : List.Perm rows'.flatten (revLabelsFrom 1 n) := by
    rw [revLabelsFrom_succ] at hperm'
    have hperm'' : List.Perm ((n + 1) :: rows'.flatten) ((n + 1) :: revLabelsFrom 1 n) := by
      simpa [Nat.add_comm] using hperm'
    exact List.Perm.cons_inv hperm''
  have hlt' : EntriesLt (n + 1) rows' := by
    intro r hr x hx
    have hx' : x ∈ rows'.flatten := List.mem_flatten_of_mem hr hx
    have hx'' : x ∈ revLabelsFrom 1 n := htail.subset hx'
    have hltx : x < 1 + n := lt_add_of_mem_revLabelsFrom hx''
    omega
  have hT' : IsRSTableau rows' := by
    have hTrecord : IsRSTableau (recordAt (n + 1) i rows') := by
      simpa [hrecord] using hT
    exact isRSTableau_of_recordAt
      (rowsNonempty_of_unrecordAt hT.1 hrec)
      hlt'
      hTrecord
  exact ⟨i, rows', hrec, hrecord, hT', hnd', htail⟩

/-- States arising from forward RS on a word with distinct letters. -/
def IsForwardImage (s : State) : Prop :=
  ∃ w, w.Nodup ∧ forward w = s

theorem backward_spec_of_isForwardImage {s : State} (hs : IsForwardImage s) :
    ∃ w, backward s = some w ∧ w.Nodup ∧ forward w = s := by
  rcases hs with ⟨w, hnd, rfl⟩
  exact ⟨w, backward_forward hnd, hnd, rfl⟩

theorem forward_injective_on_nodup {u v : List ℕ}
    (hu : u.Nodup) (hv : v.Nodup)
    (h : forward u = forward v) :
    u = v := by
  have hback := congrArg backward h
  simpa [backward_forward hu, backward_forward hv] using hback

/-- Recover the unique nodup word represented by a state in the forward image. -/
noncomputable def backwardWord (s : State) (hs : IsForwardImage s) : List ℕ :=
  Classical.choose (backward_spec_of_isForwardImage hs)

theorem backwardWord_spec {s : State} (hs : IsForwardImage s) :
    backward s = some (backwardWord s hs) ∧
    (backwardWord s hs).Nodup ∧
    forward (backwardWord s hs) = s := by
  exact Classical.choose_spec (backward_spec_of_isForwardImage hs)

/-- Robinson-Schensted as a bijection between nodup words and the image of the forward tableau
construction. The inverse direction is witnessed by the backward reconstruction algorithm. -/
noncomputable def rsCorrespondence :
    {w : List ℕ // w.Nodup} ≃ {s : State // IsForwardImage s} where
  toFun w := ⟨forward w.1, ⟨w.1, w.2, rfl⟩⟩
  invFun s := ⟨backwardWord s.1 s.2, (backwardWord_spec s.2).2.1⟩
  left_inv w := by
    apply Subtype.ext
    have hs : IsForwardImage (forward w.1) := ⟨w.1, w.2, rfl⟩
    have hspec := backwardWord_spec hs
    exact Option.some.inj (by rw [← hspec.1, backward_forward w.2])
  right_inv s := by
    apply Subtype.ext
    exact (backwardWord_spec s.2).2.2

/-- Robinson-Schensted as a bijection between permutations of `1, …, n` and concrete standard
RS tableau pairs of size `n`. -/
noncomputable def rsStandardCorrespondence (n : ℕ) :
    {w : List ℕ // List.Perm w (revLabelsFrom 1 n)} ≃ {s : State // IsStandardState n s} where
  toFun w := ⟨forward w.1, forward_isStandardState w.2⟩
  invFun s := ⟨backwardStandardWord n s.1 s.2, (backwardStandardWord_spec s.2).2.1⟩
  left_inv w := by
    apply Subtype.ext
    have hstd : IsStandardState n (forward w.1) := forward_isStandardState w.2
    have hspec := backwardStandardWord_spec (n := n) (s := forward w.1) hstd
    have hwnd : w.1.Nodup := (w.2.nodup_iff).2 (nodup_revLabelsFrom 1 n)
    have hwlen : w.1.length = n := by
      simpa [length_revLabelsFrom] using w.2.length_eq
    have hback : backwardAux n (forward w.1) = some w.1 := by
      simpa [hwlen] using backwardAux_forward hwnd
    exact Option.some.inj (by rw [← hspec.1, hback])
  right_inv s := by
    apply Subtype.ext
    exact (backwardStandardWord_spec (n := n) (s := s.1) s.2).2.2

end RS
