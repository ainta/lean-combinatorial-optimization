import Matroid.Intersection.ExchangeGraph

/-!
# Simple augmenting paths in the exchange graph

Finite alternating augmenting paths through Edmonds' exchange graph, with the existence theorem
that any nonterminal state admits one (`exists_simpleAugPath_of_not_terminal`), and the minimality
machinery used to derive the no-shortcut conditions: prefix/suffix surgery, splicing, and the
six `*_of_minimal` lemmas consumed downstream when promoting a minimal path to a `NoShortcutPath`.
-/

open Set

namespace Matroid.Intersection

variable {α : Type*} {M₁ M₂ : Matroid α} {I : Set α}

/-- A finite augmenting path with the expected alternating exchange steps, but without the
shortest-path / no-shortcut conditions. -/
structure SimpleAugPath (M₁ M₂ : Matroid α) (I : Set α) (n : ℕ) where
  x : Fin (n + 1) → α
  y : Fin n → α
  x_not_mem : ∀ i, x i ∉ I
  y_mem : ∀ i, y i ∈ I
  left_source : M₁.Indep (insert (x 0) I)
  left_step : ∀ i : Fin n, M₁.Indep (insert (xNext x i) (I \ {y i}))
  right_step : ∀ i : Fin n, M₂.Indep (insert (xPrev x i) (I \ {y i}))
  right_sink : M₂.Indep (insert (xLast x) I)

private structure SimpleSuffix (M₁ M₂ : Matroid α) (I : Set α) (n : ℕ) where
  x : Fin (n + 1) → α
  y : Fin n → α
  x_not_mem : ∀ i, x i ∉ I
  y_mem : ∀ i, y i ∈ I
  left_step : ∀ i : Fin n, M₁.Indep (insert (xNext x i) (I \ {y i}))
  right_step : ∀ i : Fin n, M₂.Indep (insert (xPrev x i) (I \ {y i}))
  right_sink : M₂.Indep (insert (xLast x) I)

private def SimpleSuffix.toSimpleAugPath {n : ℕ}
    (P : SimpleSuffix M₁ M₂ I n) (hsrc : M₁.Indep (insert (P.x 0) I)) :
    SimpleAugPath M₁ M₂ I n where
  x := P.x
  y := P.y
  x_not_mem := P.x_not_mem
  y_mem := P.y_mem
  left_source := hsrc
  left_step := P.left_step
  right_step := P.right_step
  right_sink := P.right_sink

private theorem exists_simpleSuffix_of_chain
    {x₀ : α} {l : List α}
    (hx₀_not_mem : x₀ ∉ I)
    (hchain : List.IsChain (ExchangeRel M₁ M₂ I) (x₀ :: l))
    (hsink : (x₀ :: l).getLast (by simp) ∈ SinkSet M₂ I) :
    ∃ n, ∃ P : SimpleSuffix M₁ M₂ I n, P.x 0 = x₀ := by
  cases l with
  | nil =>
      refine ⟨0, ?_⟩
      refine ⟨⟨fun _ => x₀, fun i => Fin.elim0 i, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
      · intro i
        simpa using hx₀_not_mem
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · simpa [xLast] using hsink.2
  | cons y l =>
      cases hchain with
      | cons_cons hxy htail =>
          cases l with
          | nil =>
              rcases hxy with hxy | hxy
              · exact (hx₀_not_mem hxy.1).elim
              · exact (hsink.1 hxy.2.2.1).elim
          | cons x₁ l' =>
              cases htail with
              | cons_cons hyx hrest =>
                  rcases hxy with hxy | hxy
                  · exact (hx₀_not_mem hxy.1).elim
                  ·
                    rcases hyx with hyx | hyx
                    ·
                      obtain ⟨n, P, rfl⟩ := exists_simpleSuffix_of_chain hyx.2.2.1 hrest (by
                        simpa using hsink)
                      refine ⟨n + 1, ?_⟩
                      refine
                        ⟨⟨Fin.cases x₀ (fun i => P.x i), Fin.cases y (fun i => P.y i), ?_, ?_, ?_,
                            ?_, ?_⟩, rfl⟩
                      · intro i
                        refine Fin.cases ?_ ?_ i
                        · simpa
                        · intro j
                          simpa using P.x_not_mem j
                      · intro i
                        refine Fin.cases ?_ ?_ i
                        · exact hxy.2.2.1
                        · intro j
                          simpa using P.y_mem j
                      · intro i
                        refine Fin.cases ?_ ?_ i
                        · simpa [xNext] using hyx.2.2.2
                        · intro j
                          simpa [xNext] using P.left_step j
                      · intro i
                        refine Fin.cases ?_ ?_ i
                        · simpa [xPrev] using hxy.2.2.2
                        · intro j
                          simpa [xPrev] using P.right_step j
                      · simpa [xLast] using P.right_sink
                    · exact (hyx.1 hxy.2.2.1).elim

/-- If the exchange graph is nonterminal, there is an explicit finite augmenting path. -/
theorem exists_simpleAugPath_of_not_terminal
    (hNT : ¬ Terminal M₁ M₂ I) :
    ∃ n, Nonempty (SimpleAugPath M₁ M₂ I n) := by
  rcases Set.not_disjoint_iff.mp hNT with ⟨x₀, hx₀src, hx₀reach⟩
  rcases hx₀reach with ⟨xk, hxk_sink, hx₀k⟩
  rcases List.exists_isChain_cons_of_relationReflTransGen hx₀k with ⟨l, hchain, hlast⟩
  obtain ⟨n, P, hx₀eq⟩ := exists_simpleSuffix_of_chain hx₀src.1 hchain (hlast ▸ hxk_sink)
  refine ⟨n, ?_⟩
  subst hx₀eq
  exact ⟨P.toSimpleAugPath hx₀src.2⟩

private def SimpleAugPath.prefix {n : ℕ} (P : SimpleAugPath M₁ M₂ I n)
    (m : ℕ) (hm : m ≤ n) (hsink : M₂.Indep (insert (P.x ⟨m, Nat.lt_succ_of_le hm⟩) I)) :
    SimpleAugPath M₁ M₂ I m where
  x i := P.x (Fin.castLE (Nat.succ_le_succ hm) i)
  y i := P.y (Fin.castLE hm i)
  x_not_mem i := P.x_not_mem _
  y_mem i := P.y_mem _
  left_source := by simpa using P.left_source
  left_step i := by simpa [xNext] using P.left_step (Fin.castLE hm i)
  right_step i := by simpa [xPrev] using P.right_step (Fin.castLE hm i)
  right_sink := by simpa [xLast] using hsink

private def SimpleAugPath.suffix {n : ℕ} (P : SimpleAugPath M₁ M₂ I n)
    (m : ℕ) (hm : m ≤ n) :
    SimpleSuffix M₁ M₂ I (n - m) where
  x i := P.x ⟨i.1 + m, by
    have hi := i.2
    omega⟩
  y i := P.y ⟨i.1 + m, by
    have hi := i.2
    omega⟩
  x_not_mem i := P.x_not_mem _
  y_mem i := P.y_mem _
  left_step i := by
    let j : Fin n := ⟨i.1 + m, by
      have hi := i.2
      omega⟩
    have hsucc : j.succ = ⟨i.1 + 1 + m, by
      have hi := i.2
      omega⟩ := by
      apply Fin.ext
      simp [j]
      omega
    simpa [xNext, j, hsucc] using P.left_step j
  right_step i := by
    let j : Fin n := ⟨i.1 + m, by
      have hi := i.2
      omega⟩
    simpa [xPrev, j] using P.right_step j
  right_sink := by
    simpa [xLast, Nat.sub_add_cancel hm] using P.right_sink

/-- Minimality predicate for explicit augmenting paths. -/
def SimpleAugPath.Minimal {n : ℕ} (P : SimpleAugPath M₁ M₂ I n) : Prop :=
  ∀ m, m < n → IsEmpty (SimpleAugPath M₁ M₂ I m)

/-- Any nonterminal exchange-graph state admits a length-minimal augmenting path. -/
theorem exists_minimal_simpleAugPath_of_not_terminal
    (hNT : ¬ Terminal M₁ M₂ I) :
    ∃ n, ∃ P : SimpleAugPath M₁ M₂ I n, P.Minimal := by
  classical
  have hex : ∃ n, Nonempty (SimpleAugPath M₁ M₂ I n) := exists_simpleAugPath_of_not_terminal hNT
  let n := Nat.find hex
  have hn : Nonempty (SimpleAugPath M₁ M₂ I n) := Nat.find_spec hex
  rcases hn with ⟨P⟩
  refine ⟨n, P, ?_⟩
  intro m hm
  refine ⟨fun hP => ?_⟩
  have hm' : ¬ Nonempty (SimpleAugPath M₁ M₂ I m) := Nat.find_min hex hm
  exact hm' ⟨hP⟩

/-- A minimal augmenting path admits no extra source mid-way: each interior `xNext` is not
independent over the original `I`. -/
theorem SimpleAugPath.left_not_source_of_minimal {n : ℕ}
    (P : SimpleAugPath M₁ M₂ I n) (hmin : P.Minimal) :
    ∀ i : Fin n, ¬ M₁.Indep (insert (xNext P.x i) I) := by
  intro i hsrc
  let m := i.1 + 1
  have hm : m ≤ n := by
    dsimp [m]
    omega
  let S := P.suffix m hm
  have hsrc' : M₁.Indep (insert (S.x 0) I) := by
    simpa [S, SimpleAugPath.suffix, m, xNext] using hsrc
  have hlt : n - m < n := by
    dsimp [m]
    omega
  exact (hmin (n - m) hlt).false (S.toSimpleAugPath hsrc')

/-- A minimal augmenting path admits no extra sink mid-way. -/
theorem SimpleAugPath.right_not_sink_of_minimal {n : ℕ}
    (P : SimpleAugPath M₁ M₂ I n) (hmin : P.Minimal) :
    ∀ i : Fin n, ¬ M₂.Indep (insert (xPrev P.x i) I) := by
  intro i hsink
  let m := i.1
  have hm : m ≤ n := by
    dsimp [m]
    omega
  have hsink' : M₂.Indep (insert (P.x ⟨m, Nat.lt_succ_of_le hm⟩) I) := by
    simpa [m, xPrev] using hsink
  let Q := P.prefix m hm hsink'
  have hlt : m < n := by
    dsimp [m]
    exact i.2
  exact (hmin m hlt).false Q

private def SimpleAugPath.spliceLeft {n : ℕ}
    (P : SimpleAugPath M₁ M₂ I n) {i j : Fin n} (hij : i < j)
    (hshortcut : M₁.Indep (insert (xNext P.x j) (I \ {P.y i}))) :
    SimpleAugPath M₁ M₂ I (n - (j.1 - i.1)) where
  x k :=
    if hk : k.1 ≤ i.1 then
      P.x ⟨k.1, by
        have hk' := k.2
        omega⟩
    else
      P.x ⟨k.1 + (j.1 - i.1), by
        have hk' := k.2
        omega⟩
  y k :=
    if hk : k.1 ≤ i.1 then
      P.y ⟨k.1, by
        have hk' := k.2
        omega⟩
    else
      P.y ⟨k.1 + (j.1 - i.1), by
        have hk' := k.2
        omega⟩
  x_not_mem k := by
    by_cases hk : k.1 ≤ i.1
    · simpa [hk]
        using P.x_not_mem ⟨k.1, by
          have hk' := k.2
          omega⟩
    · simpa [hk]
        using P.x_not_mem ⟨k.1 + (j.1 - i.1), by
          have hk' := k.2
          omega⟩
  y_mem k := by
    by_cases hk : k.1 ≤ i.1
    · simpa [hk]
        using P.y_mem ⟨k.1, by
          have hk' := k.2
          omega⟩
    · simpa [hk]
        using P.y_mem ⟨k.1 + (j.1 - i.1), by
          have hk' := k.2
          omega⟩
  left_source := by
    simpa
      using P.left_source
  left_step k := by
    by_cases hk_lt : k.1 < i.1
    · have hk_le : k.1 ≤ i.1 := Nat.le_of_lt hk_lt
      have hk_succ_le : k.1 + 1 ≤ i.1 := by omega
      simpa [xNext, hk_le, hk_succ_le]
        using P.left_step ⟨k.1, by
          have hk' := k.2
          omega⟩
    · by_cases hk_eq : k.1 = i.1
      · have hk_le : k.1 ≤ i.1 := hk_eq.le
        have hk_succ_gt : ¬ k.1 + 1 ≤ i.1 := by omega
        have hd : i.1 + (j.1 - i.1) = j.1 := Nat.add_sub_of_le hij.le
        have hidx :
            (⟨i.1 + 1 + (j.1 - i.1), by
              have hk' := k.2
              omega⟩ : Fin (n + 1)) = j.succ := by
          apply Fin.ext
          calc
            i.1 + 1 + (j.1 - i.1) = i.1 + (j.1 - i.1) + 1 := by omega
            _ = j.1 + 1 := by rw [hd]
        simpa [xNext, hk_le, hk_succ_gt, hk_eq, hidx] using hshortcut
      · have hk_gt : i.1 < k.1 := by omega
        have hk_ge : ¬ k.1 ≤ i.1 := by omega
        have hk_succ_ge : ¬ k.1 + 1 ≤ i.1 := by omega
        have hidx :
            (⟨k.1 + 1 + (j.1 - i.1), by
              have hk' := k.2
              omega⟩ : Fin (n + 1)) =
            (⟨k.1 + (j.1 - i.1), by
              have hk' := k.2
              omega⟩ : Fin n).succ := by
          apply Fin.ext
          calc
            k.1 + 1 + (j.1 - i.1) = (k.1 + (j.1 - i.1)) + 1 := by omega
            _ = ((⟨k.1 + (j.1 - i.1), by
                have hk' := k.2
                omega⟩ : Fin n).succ : Fin (n + 1)) := by rfl
        simpa [xNext, hk_ge, hk_succ_ge, hidx]
          using P.left_step ⟨k.1 + (j.1 - i.1), by
            have hk' := k.2
            omega⟩
  right_step k := by
    by_cases hk : k.1 ≤ i.1
    · simpa [xPrev, hk]
        using P.right_step ⟨k.1, by
          have hk' := k.2
          omega⟩
    · simpa [xPrev, hk]
        using P.right_step ⟨k.1 + (j.1 - i.1), by
          have hk' := k.2
          omega⟩
  right_sink := by
    have hlast_gt : ¬ (n - (j.1 - i.1)) ≤ i.1 := by
      have hj := j.2
      omega
    have hd : j.1 - i.1 ≤ n := by omega
    simpa [xLast, hlast_gt, Nat.sub_add_cancel hd]
      using P.right_sink

private def SimpleAugPath.spliceRight {n : ℕ}
    (P : SimpleAugPath M₁ M₂ I n) {i j : Fin n} (hij : i < j)
    (hshortcut : M₂.Indep (insert (xPrev P.x i) (I \ {P.y j}))) :
    SimpleAugPath M₁ M₂ I (n - (j.1 - i.1)) where
  x k :=
    if hk : k.1 ≤ i.1 then
      P.x ⟨k.1, by
        have hk' := k.2
        omega⟩
    else
      P.x ⟨k.1 + (j.1 - i.1), by
        have hk' := k.2
        omega⟩
  y k :=
    if hk : k.1 < i.1 then
      P.y ⟨k.1, by
        have hk' := k.2
        omega⟩
    else
      P.y ⟨k.1 + (j.1 - i.1), by
        have hk' := k.2
        omega⟩
  x_not_mem k := by
    by_cases hk : k.1 ≤ i.1
    · simpa [hk]
        using P.x_not_mem ⟨k.1, by
          have hk' := k.2
          omega⟩
    · simpa [hk]
        using P.x_not_mem ⟨k.1 + (j.1 - i.1), by
          have hk' := k.2
          omega⟩
  y_mem k := by
    by_cases hk : k.1 < i.1
    · simpa [hk]
        using P.y_mem ⟨k.1, by
          have hk' := k.2
          omega⟩
    · simpa [hk]
        using P.y_mem ⟨k.1 + (j.1 - i.1), by
          have hk' := k.2
          omega⟩
  left_source := by
    simpa
      using P.left_source
  left_step k := by
    by_cases hk_lt : k.1 < i.1
    · have hk_succ_lt : k.1 + 1 ≤ i.1 := by omega
      simpa [xNext, hk_lt, hk_succ_lt]
        using P.left_step ⟨k.1, by
          have hk' := k.2
          omega⟩
    · by_cases hk_eq : k.1 = i.1
      · have hk_y : ¬ k.1 < i.1 := by omega
        have hk_succ : ¬ k.1 + 1 ≤ i.1 := by omega
        have hd : i.1 + (j.1 - i.1) = j.1 := Nat.add_sub_of_le hij.le
        have hyidx : (⟨i.1 + (j.1 - i.1), by
          have hk' := k.2
          omega⟩ : Fin n) = j := by
          apply Fin.ext
          exact hd
        have hidx :
            (⟨i.1 + 1 + (j.1 - i.1), by
              have hk' := k.2
              omega⟩ : Fin (n + 1)) = j.succ := by
          apply Fin.ext
          calc
            i.1 + 1 + (j.1 - i.1) = i.1 + (j.1 - i.1) + 1 := by omega
            _ = j.1 + 1 := by rw [hd]
        simpa [xNext, hk_y, hk_succ, hk_eq, hyidx, hidx]
          using P.left_step j
      · have hk_gt : i.1 < k.1 := by omega
        have hk_y : ¬ k.1 < i.1 := by omega
        have hk_succ : ¬ k.1 + 1 ≤ i.1 := by omega
        have hidx :
            (⟨k.1 + 1 + (j.1 - i.1), by
              have hk' := k.2
              omega⟩ : Fin (n + 1)) =
            (⟨k.1 + (j.1 - i.1), by
              have hk' := k.2
              omega⟩ : Fin n).succ := by
          apply Fin.ext
          calc
            k.1 + 1 + (j.1 - i.1) = (k.1 + (j.1 - i.1)) + 1 := by omega
            _ = ((⟨k.1 + (j.1 - i.1), by
                have hk' := k.2
                omega⟩ : Fin n).succ : Fin (n + 1)) := by rfl
        simpa [xNext, hk_y, hk_succ, hidx]
          using P.left_step ⟨k.1 + (j.1 - i.1), by
            have hk' := k.2
            omega⟩
  right_step k := by
    by_cases hk_lt : k.1 < i.1
    · have hk_x : k.1 ≤ i.1 := Nat.le_of_lt hk_lt
      simpa [xPrev, hk_lt, hk_x]
        using P.right_step ⟨k.1, by
          have hk' := k.2
          omega⟩
    · by_cases hk_eq : k.1 = i.1
      · have hk_x : k.1 ≤ i.1 := hk_eq.le
        have hk_y : ¬ k.1 < i.1 := by omega
        have hd : i.1 + (j.1 - i.1) = j.1 := Nat.add_sub_of_le hij.le
        simpa [xPrev, hk_y, hk_x, hk_eq, hd]
          using hshortcut
      · have hk_x : ¬ k.1 ≤ i.1 := by omega
        have hk_y : ¬ k.1 < i.1 := by omega
        simpa [xPrev, hk_y, hk_x]
          using P.right_step ⟨k.1 + (j.1 - i.1), by
            have hk' := k.2
            omega⟩
  right_sink := by
    have hlast_gt : ¬ (n - (j.1 - i.1)) ≤ i.1 := by
      have hj := j.2
      omega
    have hd : j.1 - i.1 ≤ n := by omega
    simpa [xLast, hlast_gt, Nat.sub_add_cancel hd]
      using P.right_sink

/-- A minimal augmenting path admits no left shortcut between earlier and later steps. -/
theorem SimpleAugPath.left_no_shortcut_of_minimal {n : ℕ}
    (P : SimpleAugPath M₁ M₂ I n) (hmin : P.Minimal) :
    ∀ ⦃i j : Fin n⦄, i < j → ¬ M₁.Indep (insert (xNext P.x j) (I \ {P.y i})) := by
  intro i j hij hshortcut
  have hlt : n - (j.1 - i.1) < n := by omega
  exact (hmin _ hlt).false (P.spliceLeft hij hshortcut)

/-- A minimal augmenting path admits no right shortcut between earlier and later steps. -/
theorem SimpleAugPath.right_no_shortcut_of_minimal {n : ℕ}
    (P : SimpleAugPath M₁ M₂ I n) (hmin : P.Minimal) :
    ∀ ⦃i j : Fin n⦄, i < j → ¬ M₂.Indep (insert (xPrev P.x i) (I \ {P.y j})) := by
  intro i j hij hshortcut
  have hlt : n - (j.1 - i.1) < n := by omega
  exact (hmin _ hlt).false (P.spliceRight hij hshortcut)

/-- Minimal augmenting paths have injective outside-vertex sequences. -/
theorem SimpleAugPath.x_inj_of_minimal {n : ℕ}
    (P : SimpleAugPath M₁ M₂ I n) (hmin : P.Minimal) :
    Function.Injective P.x := by
  intro i j hijx
  by_cases hij : i < j
  · exfalso
    by_cases hjlast : j = Fin.last n
    · have hi_lt_n : i.1 < n := by
        rw [hjlast] at hij
        simpa using hij
      have hijlast : P.x i = P.x (Fin.last n) := by
        simpa [hjlast] using hijx
      have hsink : M₂.Indep (insert (P.x i) I) := by
        simpa [xLast, hijlast] using P.right_sink
      exact (hmin i.1 hi_lt_n).false <|
        P.prefix i.1 (Nat.le_of_lt hi_lt_n) (by simpa using hsink)
    · have hj_lt_n : j.1 < n := by
        have hj_ne_last : j.1 ≠ n := by
          intro hj_eq
          apply hjlast
          apply Fin.ext
          simpa [hj_eq]
        omega
      let i' : Fin n := ⟨i.1, by omega⟩
      let j' : Fin n := ⟨j.1, hj_lt_n⟩
      have hi_cast : i'.castSucc = i := by
        apply Fin.ext
        rfl
      have hj_cast : j'.castSucc = j := by
        apply Fin.ext
        rfl
      have hij' : i' < j' := by
        omega
      have hshortcut' : M₂.Indep (insert (P.x i) (I \ {P.y j'})) := by
        have hxij' : P.x i = xPrev P.x j' := by
          simpa [xPrev, hj_cast] using hijx
        simpa [hxij'] using P.right_step j'
      have hshortcut : M₂.Indep (insert (xPrev P.x i') (I \ {P.y j'})) := by
        simpa [xPrev, hi_cast] using hshortcut'
      have hlt : n - (j'.1 - i'.1) < n := by omega
      exact (hmin _ hlt).false (P.spliceRight hij' hshortcut)
  · by_cases hji : j < i
    · exfalso
      by_cases hilast : i = Fin.last n
      · have hj_lt_n : j.1 < n := by
          rw [hilast] at hji
          simpa using hji
        have hjlast : P.x j = P.x (Fin.last n) := by
          simpa [hilast] using hijx.symm
        have hsink : M₂.Indep (insert (P.x j) I) := by
          simpa [xLast, hjlast] using P.right_sink
        exact (hmin j.1 hj_lt_n).false <|
          P.prefix j.1 (Nat.le_of_lt hj_lt_n) (by simpa using hsink)
      · have hi_lt_n : i.1 < n := by
          have hi_ne_last : i.1 ≠ n := by
            intro hi_eq
            apply hilast
            apply Fin.ext
            simpa [hi_eq]
          omega
        let i' : Fin n := ⟨i.1, hi_lt_n⟩
        let j' : Fin n := ⟨j.1, by omega⟩
        have hi_cast : i'.castSucc = i := by
          apply Fin.ext
          rfl
        have hj_cast : j'.castSucc = j := by
          apply Fin.ext
          rfl
        have hji' : j' < i' := by
          omega
        have hshortcut' : M₂.Indep (insert (P.x j) (I \ {P.y i'})) := by
          have hxji' : P.x j = xPrev P.x i' := by
            simpa [xPrev, hi_cast] using hijx.symm
          simpa [hxji'] using P.right_step i'
        have hshortcut : M₂.Indep (insert (xPrev P.x j') (I \ {P.y i'})) := by
          simpa [xPrev, hj_cast] using hshortcut'
        have hlt : n - (i'.1 - j'.1) < n := by omega
        exact (hmin _ hlt).false (P.spliceRight hji' hshortcut)
    · apply Fin.ext
      omega

/-- Minimal augmenting paths have injective inside-vertex sequences. -/
theorem SimpleAugPath.y_inj_of_minimal {n : ℕ}
    (P : SimpleAugPath M₁ M₂ I n) (hmin : P.Minimal) :
    Function.Injective P.y := by
  intro i j hijy
  by_cases hij : i < j
  · exfalso
    have hshortcut : M₁.Indep (insert (xNext P.x j) (I \ {P.y i})) := by
      simpa [hijy] using P.left_step j
    have hlt : n - (j.1 - i.1) < n := by omega
    exact (hmin _ hlt).false (P.spliceLeft hij hshortcut)
  · by_cases hji : j < i
    · exfalso
      have hshortcut : M₁.Indep (insert (xNext P.x i) (I \ {P.y j})) := by
        simpa [hijy.symm] using P.left_step i
      have hlt : n - (i.1 - j.1) < n := by omega
      exact (hmin _ hlt).false (P.spliceLeft hji hshortcut)
    · apply Fin.ext
      omega

end Matroid.Intersection
