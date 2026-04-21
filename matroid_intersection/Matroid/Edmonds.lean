import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Set.Card

open Set

namespace Matroid

variable {α : Type*}

/-- A set is common independent for two matroids if it is independent in both. -/
def CommonIndep (M₁ M₂ : Matroid α) (I : Set α) : Prop :=
  M₁.Indep I ∧ M₂.Indep I

/-- The result of augmenting `I` along the length-one alternating path
`x₀ → y → x₁`. -/
def augmentLengthOne (I : Set α) (y x₀ x₁ : α) : Set α :=
  insert x₀ (insert x₁ (I \ {y}))

namespace Edmonds

variable {M₁ M₂ : Matroid α} {I : Set α} {y x₀ x₁ : α}

/-- The two matroids in a matroid-intersection instance share the same ground set. -/
def SameGround (M₁ M₂ : Matroid α) : Prop :=
  M₁.E = M₂.E

/-- The result of augmenting `I` along a finite alternating path with outside vertices `x`
and inside vertices `y`. -/
def augmentPath (I : Set α) {n : ℕ} (x : Fin (n + 1) → α) (y : Fin n → α) : Set α :=
  (I \ Set.range y) ∪ Set.range x

private def xPrev {n : ℕ} (x : Fin (n + 1) → α) (i : Fin n) : α :=
  x i.castSucc

private def xNext {n : ℕ} (x : Fin (n + 1) → α) (i : Fin n) : α :=
  x i.succ

private def xLast {n : ℕ} (x : Fin (n + 1) → α) : α :=
  x (Fin.last n)

/-- The left exchange relation `y → x` in the exchange graph of `M` at `I`. -/
def LeftArc (M : Matroid α) (I : Set α) (y x : α) : Prop :=
  M.Indep (insert x (I \ {y}))

/-- The source set for the first matroid in Edmonds' exchange graph. -/
def SourceSet (M : Matroid α) (I : Set α) : Set α :=
  {x | x ∉ I ∧ M.Indep (insert x I)}

/-- The sink set for the second matroid in Edmonds' exchange graph. -/
def SinkSet (M : Matroid α) (I : Set α) : Set α :=
  {x | x ∉ I ∧ M.Indep (insert x I)}

/-- The directed exchange relation for matroid intersection. -/
def ExchangeRel (M₁ M₂ : Matroid α) (I : Set α) (u v : α) : Prop :=
  (u ∈ I ∧ u ≠ v ∧ v ∉ I ∧ LeftArc M₁ I u v) ∨
    (u ∉ I ∧ u ≠ v ∧ v ∈ I ∧ LeftArc M₂ I v u)

/-- A terminal certificate for Edmonds' algorithm: `U` contains all sinks, is closed backwards
under exchange arcs, and contains no source. -/
structure TerminalCertificate (M₁ M₂ : Matroid α) (I U : Set α) : Prop where
  sinks_subset : SinkSet M₂ I ⊆ U
  left_closed : ∀ ⦃y x⦄, y ∈ I → x ∉ I → LeftArc M₁ I y x → x ∈ U → y ∈ U
  right_closed : ∀ ⦃x y⦄, x ∉ I → y ∈ I → LeftArc M₂ I y x → y ∈ U → x ∈ U
  source_disjoint : Disjoint (SourceSet M₁ I) U

/-- The vertices that can reach some sink in Edmonds' exchange graph. -/
def ReachableToSink (M₁ M₂ : Matroid α) (I : Set α) : Set α :=
  {z | ∃ x ∈ SinkSet M₂ I, Relation.ReflTransGen (ExchangeRel M₁ M₂ I) z x}

/-- The exchange-graph terminal condition used by Edmonds' algorithm. -/
def Terminal (M₁ M₂ : Matroid α) (I : Set α) : Prop :=
  Disjoint (SourceSet M₁ I) (ReachableToSink M₁ M₂ I)

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

private theorem exists_minimal_simpleAugPath_of_not_terminal
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

private theorem SimpleAugPath.left_not_source_of_minimal {n : ℕ}
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

private theorem SimpleAugPath.right_not_sink_of_minimal {n : ℕ}
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

private theorem SimpleAugPath.left_no_shortcut_of_minimal {n : ℕ}
    (P : SimpleAugPath M₁ M₂ I n) (hmin : P.Minimal) :
    ∀ ⦃i j : Fin n⦄, i < j → ¬ M₁.Indep (insert (xNext P.x j) (I \ {P.y i})) := by
  intro i j hij hshortcut
  have hlt : n - (j.1 - i.1) < n := by omega
  exact (hmin _ hlt).false (P.spliceLeft hij hshortcut)

private theorem SimpleAugPath.right_no_shortcut_of_minimal {n : ℕ}
    (P : SimpleAugPath M₁ M₂ I n) (hmin : P.Minimal) :
    ∀ ⦃i j : Fin n⦄, i < j → ¬ M₂.Indep (insert (xPrev P.x i) (I \ {P.y j})) := by
  intro i j hij hshortcut
  have hlt : n - (j.1 - i.1) < n := by omega
  exact (hmin _ hlt).false (P.spliceRight hij hshortcut)

private theorem SimpleAugPath.x_inj_of_minimal {n : ℕ}
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

private theorem SimpleAugPath.y_inj_of_minimal {n : ℕ}
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

/-- A no-shortcut augmenting path for Edmonds' algorithm, encoded by the outside vertices
`x₀, …, xₙ` and the inside vertices `y₀, …, yₙ₋₁`. The `M₁` conditions are oriented from
left to right, while the `M₂` conditions are oriented from right to left. -/
structure NoShortcutPath (M₁ M₂ : Matroid α) (I : Set α) (n : ℕ) where
  x : Fin (n + 1) → α
  y : Fin n → α
  x_not_mem : ∀ i, x i ∉ I
  y_mem : ∀ i, y i ∈ I
  x_inj : Function.Injective x
  y_inj : Function.Injective y
  disjoint : ∀ i j, x i ≠ y j
  left_source : M₁.Indep (insert (x 0) I)
  left_not_source : ∀ i : Fin n, ¬ M₁.Indep (insert (xNext x i) I)
  left_step : ∀ i : Fin n, M₁.Indep (insert (xNext x i) (I \ {y i}))
  left_no_shortcut : ∀ ⦃i j : Fin n⦄, i < j → ¬ M₁.Indep (insert (xNext x j) (I \ {y i}))
  right_step : ∀ i : Fin n, M₂.Indep (insert (xPrev x i) (I \ {y i}))
  right_sink : M₂.Indep (insert (xLast x) I)
  right_not_sink : ∀ i : Fin n, ¬ M₂.Indep (insert (xPrev x i) I)
  right_no_shortcut : ∀ ⦃i j : Fin n⦄, i < j → ¬ M₂.Indep (insert (xPrev x i) (I \ {y j}))

/-- Forget the no-shortcut / shortest-path conditions from a certified path. -/
def NoShortcutPath.toSimpleAugPath {n : ℕ} (P : NoShortcutPath M₁ M₂ I n) :
    SimpleAugPath M₁ M₂ I n where
  x := P.x
  y := P.y
  x_not_mem := P.x_not_mem
  y_mem := P.y_mem
  left_source := P.left_source
  left_step := P.left_step
  right_step := P.right_step
  right_sink := P.right_sink

/-- A minimal explicit augmenting path satisfies the no-shortcut certificate. -/
def SimpleAugPath.toNoShortcutPath {n : ℕ}
    (P : SimpleAugPath M₁ M₂ I n) (hmin : P.Minimal) :
    NoShortcutPath M₁ M₂ I n where
  x := P.x
  y := P.y
  x_not_mem := P.x_not_mem
  y_mem := P.y_mem
  x_inj := P.x_inj_of_minimal hmin
  y_inj := P.y_inj_of_minimal hmin
  disjoint i j := by
    intro h
    exact P.x_not_mem i (h ▸ P.y_mem j)
  left_source := P.left_source
  left_not_source := P.left_not_source_of_minimal hmin
  left_step := P.left_step
  left_no_shortcut := P.left_no_shortcut_of_minimal hmin
  right_step := P.right_step
  right_sink := P.right_sink
  right_not_sink := P.right_not_sink_of_minimal hmin
  right_no_shortcut := P.right_no_shortcut_of_minimal hmin

/-- One abstract augmentation step of Edmonds' algorithm, certified by a `NoShortcutPath`. -/
def AugmentStep (M₁ M₂ : Matroid α) (I J : Set α) : Prop :=
  ∃ n, ∃ P : NoShortcutPath M₁ M₂ I n, J = augmentPath I P.x P.y

/-- A run of Edmonds-style augmentations certified by `NoShortcutPath` witnesses. -/
abbrev Run (M₁ M₂ : Matroid α) (I J : Set α) : Prop :=
  Relation.ReflTransGen (AugmentStep M₁ M₂) I J

/-- If the exchange graph is nonterminal, there is a certified no-shortcut augmenting path. -/
theorem exists_noShortcutPath_of_not_terminal
    (hNT : ¬ Terminal M₁ M₂ I) :
    ∃ n, Nonempty (NoShortcutPath M₁ M₂ I n) := by
  rcases exists_minimal_simpleAugPath_of_not_terminal hNT with ⟨n, P, hmin⟩
  exact ⟨n, ⟨P.toNoShortcutPath hmin⟩⟩

/-- Nonterminal states admit a certified augmentation step. -/
theorem exists_augmentStep_of_nonterminal
    (hNT : ¬ Terminal M₁ M₂ I) :
    ∃ J, AugmentStep M₁ M₂ I J := by
  rcases exists_noShortcutPath_of_not_terminal hNT with ⟨n, ⟨P⟩⟩
  exact ⟨augmentPath I P.x P.y, ⟨n, P, rfl⟩⟩

private theorem NoShortcutPath.source_arc {n : ℕ} (P : NoShortcutPath M₁ M₂ I n) (i : Fin n) :
    ExchangeRel M₁ M₂ I (xPrev P.x i) (P.y i) := by
  right
  refine ⟨P.x_not_mem _, ?_, P.y_mem i, P.right_step i⟩
  simpa [xPrev] using P.disjoint i.castSucc i

private theorem NoShortcutPath.sink_arc {n : ℕ} (P : NoShortcutPath M₁ M₂ I n) (i : Fin n) :
    ExchangeRel M₁ M₂ I (P.y i) (xNext P.x i) := by
  left
  refine ⟨P.y_mem i, ?_, P.x_not_mem _, P.left_step i⟩
  intro h
  exact P.disjoint i.succ i h.symm

private theorem NoShortcutPath.reaches_sink_from {n : ℕ} (P : NoShortcutPath M₁ M₂ I n)
    (m : ℕ) (hm : m ≤ n) :
    Relation.ReflTransGen (ExchangeRel M₁ M₂ I)
      (P.x ⟨m, Nat.lt_succ_of_le hm⟩) (xLast P.x) := by
  refine Nat.decreasingInduction ?_ ?_ hm
  · intro k hk hrec
    let i : Fin n := ⟨k, hk⟩
    have hxy : ExchangeRel M₁ M₂ I (P.x ⟨k, Nat.lt_succ_of_lt hk⟩) (P.y i) := by
      simpa [i, xPrev]
        using P.source_arc i
    have hyx :
        ExchangeRel M₁ M₂ I (P.y i) (P.x ⟨k + 1, Nat.succ_lt_succ hk⟩) := by
      simpa [i, xNext]
        using P.sink_arc i
    exact Relation.ReflTransGen.head hxy (Relation.ReflTransGen.head hyx hrec)
  · simpa [xLast, Fin.last] using
      (Relation.ReflTransGen.refl :
        Relation.ReflTransGen (ExchangeRel M₁ M₂ I) (P.x (Fin.last n)) (P.x (Fin.last n)))

/-- A certified no-shortcut path really does start at a source and reach a sink in the exchange
graph. -/
theorem NoShortcutPath.source_mem_reachableToSink {n : ℕ} (P : NoShortcutPath M₁ M₂ I n) :
    P.x 0 ∈ SourceSet M₁ I ∩ ReachableToSink M₁ M₂ I := by
  refine ⟨⟨P.x_not_mem 0, P.left_source⟩, ?_⟩
  refine ⟨xLast P.x, ⟨P.x_not_mem _, P.right_sink⟩, ?_⟩
  simpa using P.reaches_sink_from 0 (Nat.zero_le n)

/-- If the terminal exchange-graph condition holds, then no certified no-shortcut augmenting path
exists. -/
theorem no_noShortcutPath_of_terminal
    (hTerm : Terminal M₁ M₂ I) {n : ℕ} :
    IsEmpty (NoShortcutPath M₁ M₂ I n) := by
  refine ⟨fun P ↦ ?_⟩
  have hx : P.x 0 ∈ SourceSet M₁ I ∩ ReachableToSink M₁ M₂ I := P.source_mem_reachableToSink
  exact (Set.disjoint_left.mp hTerm hx.1) hx.2

/-- Terminal states admit no certified augmentation step. -/
theorem no_augmentStep_of_terminal
    (hTerm : Terminal M₁ M₂ I) :
    ¬ ∃ J, AugmentStep M₁ M₂ I J := by
  rintro ⟨J, n, P, rfl⟩
  exact (no_noShortcutPath_of_terminal (M₁ := M₁) (M₂ := M₂) (I := I) hTerm).false P

/-- If no certified augmentation step exists, the exchange graph is terminal. -/
theorem terminal_of_no_augmentStep
    (hNo : ¬ ∃ J, AugmentStep M₁ M₂ I J) :
    Terminal M₁ M₂ I := by
  by_contra hTerm
  exact hNo (exists_augmentStep_of_nonterminal hTerm)

/-- A state is terminal exactly when no certified augmentation step is available. -/
theorem terminal_iff_no_augmentStep :
    Terminal M₁ M₂ I ↔ ¬ ∃ J, AugmentStep M₁ M₂ I J := by
  constructor
  · exact no_augmentStep_of_terminal
  · exact terminal_of_no_augmentStep

private theorem left_indep_of_noShortcut {n : ℕ}
    (hI : M₁.Indep I) (P : NoShortcutPath M₁ M₂ I n) :
    M₁.Indep (augmentPath I P.x P.y) := by
  classical
  let J : Set α := augmentPath I P.x P.y
  have hx_ground : ∀ i, P.x i ∈ M₁.E := by
    intro i
    refine Fin.cases ?_ ?_ i
    · exact P.left_source.subset_ground (by simp)
    · intro j
      simpa [xNext] using (P.left_step j).subset_ground (by simp [xNext])
  have hJ_ground : J ⊆ M₁.E := by
    intro z hz
    rcases hz with hz | hz
    · exact hI.subset_ground hz.1
    · rcases hz with ⟨i, rfl⟩
      exact hx_ground i
  by_contra hJ
  have hJ_dep : M₁.Dep J := (not_indep_iff hJ_ground).1 hJ
  obtain ⟨C, hCJ, hC⟩ := hJ_dep.exists_isCircuit_subset
  have hxC : ∃ i, P.x i ∈ C := by
    by_contra hnone
    have hCI : C ⊆ I := by
      intro z hz
      have hzJ := hCJ hz
      rcases hzJ with hzI | hzX
      · exact hzI.1
      · rcases hzX with ⟨i, rfl⟩
        exact False.elim (hnone ⟨i, by simpa⟩)
    exact hC.dep.not_indep (hI.subset hCI)
  let s : Finset (Fin (n + 1)) := Finset.univ.filter fun i => P.x i ∈ C
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hxC
    exact ⟨i, by simp [s, hi]⟩
  let j : Fin (n + 1) := s.min' hs
  have hjC : P.x j ∈ C := by
    exact (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  have hjmin : ∀ {k}, P.x k ∈ C → j ≤ k := by
    intro k hk
    exact Finset.min'_le s k (by simp [s, hk])
  revert hjC hjmin
  refine Fin.cases ?_ ?_ j
  · intro hjC hjmin
    have hx0_not_closure : P.x 0 ∉ M₁.closure I := by
      have hsrc := P.left_source
      rw [hI.insert_indep_iff_of_notMem (P.x_not_mem 0)] at hsrc
      exact hsrc.2
    have hsubset : C \ {P.x 0} ⊆ M₁.closure I := by
      intro z hz
      have hzC : z ∈ C := hz.1
      have hzneq : z ≠ P.x 0 := by simpa using hz.2
      have hzJ := hCJ hzC
      rcases hzJ with hzI | hzX
      · exact M₁.subset_closure I hI.subset_ground hzI.1
      · rcases hzX with ⟨k, rfl⟩
        have hk_ne_zero : k ≠ 0 := by
          intro hk
          exact hzneq (by simpa [hk])
        have hk_not_source : ¬ M₁.Indep (insert (P.x k) I) := by
          simpa [xNext] using P.left_not_source (Fin.pred k hk_ne_zero)
        have hk_not_mem : P.x k ∉ I := P.x_not_mem k
        have hk_ground : P.x k ∈ M₁.E := hx_ground k
        by_contra hk_closure
        exact hk_not_source ((hI.insert_indep_iff_of_notMem hk_not_mem).2 ⟨hk_ground, hk_closure⟩)
    exact hx0_not_closure <|
      M₁.closure_subset_closure_of_subset_closure hsubset
        (hC.mem_closure_diff_singleton_of_mem hjC)
  · intro i hjC hjmin
    have hx_not_closure : P.x i.succ ∉ M₁.closure (I \ {P.y i}) := by
      have hstep := P.left_step i
      have hdiff : M₁.Indep (I \ {P.y i}) := hI.diff _
      have hx_not_mem : P.x i.succ ∉ I \ {P.y i} := by
        simp [P.x_not_mem]
      rw [xNext, hdiff.insert_indep_iff_of_notMem hx_not_mem] at hstep
      exact hstep.2
    have hsubset : C \ {P.x i.succ} ⊆ M₁.closure (I \ {P.y i}) := by
      intro z hz
      have hzC : z ∈ C := hz.1
      have hzneq : z ≠ P.x i.succ := by simpa using hz.2
      have hzJ := hCJ hzC
      rcases hzJ with hzI | hzX
      · exact M₁.subset_closure (I \ {P.y i}) (diff_subset.trans hI.subset_ground) <| by
          refine ⟨hzI.1, ?_⟩
          intro hz_y
          exact hzI.2 ⟨i, hz_y.symm⟩
      · rcases hzX with ⟨k, rfl⟩
        have hk_ge : i.succ ≤ k := hjmin (by simpa using hzC)
        have hk_ne : k ≠ i.succ := by
          intro hk
          exact hzneq (by simpa [hk])
        have hk_gt : i.succ < k := lt_of_le_of_ne hk_ge hk_ne.symm
        have hk_ne_zero : k ≠ 0 := by
          intro hk
          simpa [hk] using hk_gt
        have hshortcut : ¬ M₁.Indep (insert (P.x k) (I \ {P.y i})) := by
          have hik : i < Fin.pred k hk_ne_zero := (Fin.lt_pred_iff hk_ne_zero).2 hk_gt
          simpa [xNext] using P.left_no_shortcut hik
        have hk_not_mem : P.x k ∉ I \ {P.y i} := by
          simp [P.x_not_mem]
        have hk_ground : P.x k ∈ M₁.E := hx_ground k
        have hdiff : M₁.Indep (I \ {P.y i}) := hI.diff _
        by_contra hk_closure
        exact hshortcut ((hdiff.insert_indep_iff_of_notMem hk_not_mem).2 ⟨hk_ground, hk_closure⟩)
    exact hx_not_closure <|
      M₁.closure_subset_closure_of_subset_closure hsubset
        (hC.mem_closure_diff_singleton_of_mem hjC)

private theorem right_indep_of_noShortcut {n : ℕ}
    (hI : M₂.Indep I) (P : NoShortcutPath M₁ M₂ I n) :
    M₂.Indep (augmentPath I P.x P.y) := by
  classical
  let J : Set α := augmentPath I P.x P.y
  have hx_ground : ∀ i, P.x i ∈ M₂.E := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa [xLast] using P.right_sink.subset_ground (by simp [xLast])
    · intro j
      simpa [xPrev] using (P.right_step j).subset_ground (by simp [xPrev])
  have hJ_ground : J ⊆ M₂.E := by
    intro z hz
    rcases hz with hz | hz
    · exact hI.subset_ground hz.1
    · rcases hz with ⟨i, rfl⟩
      exact hx_ground i
  by_contra hJ
  have hJ_dep : M₂.Dep J := (not_indep_iff hJ_ground).1 hJ
  obtain ⟨C, hCJ, hC⟩ := hJ_dep.exists_isCircuit_subset
  have hxC : ∃ i, P.x i ∈ C := by
    by_contra hnone
    have hCI : C ⊆ I := by
      intro z hz
      have hzJ := hCJ hz
      rcases hzJ with hzI | hzX
      · exact hzI.1
      · rcases hzX with ⟨i, rfl⟩
        exact False.elim (hnone ⟨i, by simpa⟩)
    exact hC.dep.not_indep (hI.subset hCI)
  let s : Finset (Fin (n + 1)) := Finset.univ.filter fun i => P.x i ∈ C
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hxC
    exact ⟨i, by simp [s, hi]⟩
  let j : Fin (n + 1) := s.max' hs
  have hjC : P.x j ∈ C := by
    exact (Finset.mem_filter.mp (Finset.max'_mem s hs)).2
  have hjmax : ∀ {k}, P.x k ∈ C → k ≤ j := by
    intro k hk
    exact Finset.le_max' s k (by simp [s, hk])
  revert hjC hjmax
  refine Fin.lastCases ?_ ?_ j
  · intro hjC hjmax
    have hxlast_not_closure : xLast P.x ∉ M₂.closure I := by
      have hsink := P.right_sink
      rw [xLast, hI.insert_indep_iff_of_notMem (P.x_not_mem _)] at hsink
      exact hsink.2
    have hsubset : C \ {xLast P.x} ⊆ M₂.closure I := by
      intro z hz
      have hzC : z ∈ C := hz.1
      have hzneq : z ≠ xLast P.x := by simpa [xLast] using hz.2
      have hzJ := hCJ hzC
      rcases hzJ with hzI | hzX
      · exact M₂.subset_closure I hI.subset_ground hzI.1
      · rcases hzX with ⟨k, rfl⟩
        cases k using Fin.lastCases with
        | last =>
            exfalso
            exact hzneq rfl
        | cast k =>
            have hk_not_sink : ¬ M₂.Indep (insert (P.x k.castSucc) I) := P.right_not_sink k
            have hk_not_mem : P.x k.castSucc ∉ I := P.x_not_mem _
            have hk_ground : P.x k.castSucc ∈ M₂.E := hx_ground _
            by_contra hk_closure
            exact hk_not_sink ((hI.insert_indep_iff_of_notMem hk_not_mem).2 ⟨hk_ground, hk_closure⟩)
    exact hxlast_not_closure <|
      M₂.closure_subset_closure_of_subset_closure hsubset
        (hC.mem_closure_diff_singleton_of_mem hjC)
  · intro i hjC hjmax
    have hx_not_closure : xPrev P.x i ∉ M₂.closure (I \ {P.y i}) := by
      have hstep := P.right_step i
      have hdiff : M₂.Indep (I \ {P.y i}) := hI.diff _
      have hx_not_mem : xPrev P.x i ∉ I \ {P.y i} := by
        simp [xPrev, P.x_not_mem]
      have hstep' : M₂.Indep (insert (xPrev P.x i) (I \ {P.y i})) := by
        simpa [xPrev] using hstep
      rw [hdiff.insert_indep_iff_of_notMem hx_not_mem] at hstep'
      exact hstep'.2
    have hsubset : C \ {xPrev P.x i} ⊆ M₂.closure (I \ {P.y i}) := by
      intro z hz
      have hzC : z ∈ C := hz.1
      have hzneq : z ≠ xPrev P.x i := by simpa [xPrev] using hz.2
      have hzJ := hCJ hzC
      rcases hzJ with hzI | hzX
      · exact M₂.subset_closure (I \ {P.y i}) (diff_subset.trans hI.subset_ground) <| by
          refine ⟨hzI.1, ?_⟩
          intro hz_y
          exact hzI.2 ⟨i, hz_y.symm⟩
      · rcases hzX with ⟨k, rfl⟩
        have hk_le : k ≤ i.castSucc := hjmax (by simpa using hzC)
        have hk_ne : k ≠ i.castSucc := by
          intro hk
          exact hzneq (by simpa [xPrev, hk])
        have hk_lt : k < i.castSucc := lt_of_le_of_ne hk_le hk_ne
        cases k using Fin.lastCases with
        | last =>
            exfalso
            exact not_lt_of_ge (Fin.le_last _) hk_lt
        | cast k =>
            have hk_lt' : k < i := by simpa using hk_lt
            have hshortcut : ¬ M₂.Indep (insert (P.x k.castSucc) (I \ {P.y i})) := by
              simpa [xPrev] using P.right_no_shortcut hk_lt'
            have hk_not_mem : P.x k.castSucc ∉ I \ {P.y i} := by
              simp [P.x_not_mem]
            have hk_ground : P.x k.castSucc ∈ M₂.E := hx_ground _
            have hdiff : M₂.Indep (I \ {P.y i}) := hI.diff _
            by_contra hk_closure
            exact hshortcut ((hdiff.insert_indep_iff_of_notMem hk_not_mem).2 ⟨hk_ground, hk_closure⟩)
    exact hx_not_closure <|
      M₂.closure_subset_closure_of_subset_closure hsubset
        (hC.mem_closure_diff_singleton_of_mem hjC)

/-- Augmenting along a no-shortcut path preserves common independence. -/
theorem NoShortcutPath.commonIndep_augment {n : ℕ}
    (hI : CommonIndep M₁ M₂ I) (P : NoShortcutPath M₁ M₂ I n) :
    CommonIndep M₁ M₂ (augmentPath I P.x P.y) := by
  exact ⟨left_indep_of_noShortcut hI.1 P, right_indep_of_noShortcut hI.2 P⟩

/-- A certified augmentation step preserves common independence. -/
theorem augmentStep_commonIndep {I J : Set α}
    (hI : CommonIndep M₁ M₂ I) (hStep : AugmentStep M₁ M₂ I J) :
    CommonIndep M₁ M₂ J := by
  rcases hStep with ⟨n, P, rfl⟩
  exact P.commonIndep_augment hI

/-- Common independence is preserved along any certified augmentation run. -/
theorem commonIndep_of_run {I₀ I : Set α}
    (h₀ : CommonIndep M₁ M₂ I₀) (hRun : Run M₁ M₂ I₀ I) :
    CommonIndep M₁ M₂ I := by
  induction hRun with
  | refl =>
      exact h₀
  | @tail K L hRun hStep ih =>
      exact augmentStep_commonIndep ih hStep

section NoShortcutCardinality

variable [Finite α]

/-- A no-shortcut augmenting path increases the size of the current common independent set by one. -/
theorem NoShortcutPath.ncard_augment {n : ℕ} (P : NoShortcutPath M₁ M₂ I n) :
    (augmentPath I P.x P.y).ncard = I.ncard + 1 := by
  classical
  have hy_subset : Set.range P.y ⊆ I := by
    rintro _ ⟨i, rfl⟩
    exact P.y_mem i
  have hdisj : Disjoint (I \ Set.range P.y) (Set.range P.x) := by
    refine disjoint_left.2 ?_
    intro z hzI hzX
    rcases hzX with ⟨i, rfl⟩
    exact P.x_not_mem i hzI.1
  have hy_card : (Set.range P.y).ncard = n := by
    simpa using Set.ncard_range_of_injective P.y_inj
  have hx_card : (Set.range P.x).ncard = n + 1 := by
    simpa using Set.ncard_range_of_injective P.x_inj
  have hdiff : (I \ Set.range P.y).ncard = I.ncard - n := by
    simpa [hy_card] using Set.ncard_diff hy_subset
  have hy_le : n ≤ I.ncard := by
    rw [← hy_card]
    exact Set.ncard_le_ncard hy_subset
  calc
    (augmentPath I P.x P.y).ncard = (I \ Set.range P.y).ncard + (Set.range P.x).ncard := by
      rw [augmentPath, Set.ncard_union_eq hdisj]
    _ = (I.ncard - n) + (n + 1) := by rw [hdiff, hx_card]
    _ = I.ncard + 1 := by rw [← Nat.add_assoc, Nat.sub_add_cancel hy_le]

/-- A certified augmentation step increases the current set size by one. -/
theorem augmentStep_ncard {I J : Set α}
    (hStep : AugmentStep M₁ M₂ I J) :
    J.ncard = I.ncard + 1 := by
  rcases hStep with ⟨n, P, rfl⟩
  exact P.ncard_augment

/-- Certified augmentation cannot continue forever: the reverse step relation is well-founded
because each step strictly increases cardinality. -/
theorem augmentStep_wf : WellFounded (flip (AugmentStep M₁ M₂)) := by
  let _ := Fintype.ofFinite α
  refine
    Subrelation.wf
      (r := (measure fun I : Set α => Fintype.card α - I.ncard).rel)
      ?_ ((measure fun I : Set α => Fintype.card α - I.ncard).wf)
  intro A B hStep
  change Fintype.card α - A.ncard < Fintype.card α - B.ncard
  have hcard : A.ncard = B.ncard + 1 := augmentStep_ncard hStep
  have hA_le : A.ncard ≤ Fintype.card α := by
    simpa using Set.ncard_le_ncard (s := A) (t := Set.univ) (by intro x hx; simp)
  omega

end NoShortcutCardinality

section TerminalOptimality

variable [Finite α] {U J : Set α}

private theorem left_rank_eq_of_certificate
    (_hE : SameGround M₁ M₂) (hI : CommonIndep M₁ M₂ I)
    (hU : TerminalCertificate M₁ M₂ I U) :
    M₁.eRk U = (I ∩ U).encard := by
  have hIU_indep : M₁.Indep (I ∩ U) := hI.1.subset inter_subset_left
  apply le_antisymm
  · by_contra hlt
    have hlt' : M₁.eRk (I ∩ U) < M₁.eRk U := by
      have hlt' : (I ∩ U).encard < M₁.eRk U := lt_of_not_ge hlt
      rwa [← hIU_indep.eRk_eq_encard] at hlt'
    obtain ⟨x, hxU, hxrank⟩ := M₁.exists_eRk_insert_eq_add_one_of_lt hlt'
    have hx_mem_U : x ∈ U := hxU.1
    have hx_not_mem_IU : x ∉ I ∩ U := hxU.2
    have hx_not_mem_I : x ∉ I := by
      intro hxI
      exact hxU.2 ⟨hxI, hxU.1⟩
    have hx_insert_indep : M₁.Indep (insert x (I ∩ U)) := by
      refine (M₁.indep_iff_eRk_eq_encard_of_finite (I := insert x (I ∩ U)) (by toFinite_tac)).2 ?_
      simpa [Set.encard_insert_of_notMem hx_not_mem_IU, hIU_indep.eRk_eq_encard] using hxrank
    have hx_ground : x ∈ M₁.E := hx_insert_indep.subset_ground (by simp)
    have hx_not_source : ¬ M₁.Indep (insert x I) := by
      intro hxsrc
      have hx_not_source_set : x ∉ SourceSet M₁ I := (disjoint_right.mp hU.source_disjoint) hx_mem_U
      exact hx_not_source_set ⟨hx_not_mem_I, hxsrc⟩
    have hx_closure : x ∈ M₁.closure I := by
      by_contra hx_not_closure
      exact hx_not_source <|
        (hI.1.insert_indep_iff_of_notMem hx_not_mem_I).2 ⟨hx_ground, hx_not_closure⟩
    have hx_not_closure_IU : x ∉ M₁.closure (I ∩ U) := by
      have htmp := hx_insert_indep
      rw [hIU_indep.insert_indep_iff_of_notMem hx_not_mem_IU] at htmp
      exact htmp.2
    have hfund : M₁.IsCircuit (M₁.fundCircuit x I) := hI.1.fundCircuit_isCircuit hx_closure hx_not_mem_I
    obtain ⟨y, hyDiff, hyNotU⟩ : ∃ y, y ∈ M₁.fundCircuit x I \ {x} ∧ y ∉ U := by
      by_contra hnone
      have hallU : M₁.fundCircuit x I \ {x} ⊆ I ∩ U := by
        intro y hy
        refine ⟨?_, ?_⟩
        · rw [M₁.fundCircuit_diff_eq_inter hx_not_mem_I] at hy
          exact hy.2
        · by_contra hyU
          exact hnone ⟨y, hy, hyU⟩
      exact hx_not_closure_IU <|
        M₁.closure_subset_closure hallU (hfund.mem_closure_diff_singleton_of_mem (M₁.mem_fundCircuit x I))
    have hyFund : y ∈ M₁.fundCircuit x I := hyDiff.1
    have hy_mem_I : y ∈ I := by
      rw [M₁.fundCircuit_diff_eq_inter hx_not_mem_I] at hyDiff
      exact hyDiff.2
    have hy_ne : y ≠ x := by simpa using hyDiff.2
    have hy_step' : M₁.Indep (insert x I \ {y}) := (hI.1.mem_fundCircuit_iff hx_closure hx_not_mem_I).1 hyFund
    have hy_step : LeftArc M₁ I y x := by
      dsimp [LeftArc]
      simpa [insert_diff_singleton_comm hy_ne.symm, hx_not_mem_I] using hy_step'
    exact hyNotU (hU.left_closed hy_mem_I hx_not_mem_I hy_step hx_mem_U)
  · exact hIU_indep.encard_le_eRk_of_subset inter_subset_right

private theorem right_rank_eq_of_certificate
    (hE : SameGround M₁ M₂) (hI : CommonIndep M₁ M₂ I)
    (hU : TerminalCertificate M₁ M₂ I U) :
    M₂.eRk (M₁.E \ U) = (I \ U).encard := by
  have hI_diff_indep : M₂.Indep (I \ U) := hI.2.subset diff_subset
  apply le_antisymm
  · by_contra hlt
    have hlt' : M₂.eRk (I \ U) < M₂.eRk (M₁.E \ U) := by
      have hlt' : (I \ U).encard < M₂.eRk (M₁.E \ U) := lt_of_not_ge hlt
      rwa [← hI_diff_indep.eRk_eq_encard] at hlt'
    obtain ⟨x, hxEU, hxrank⟩ := M₂.exists_eRk_insert_eq_add_one_of_lt hlt'
    have hx_ground₁ : x ∈ M₁.E := hxEU.1.1
    have hx_not_mem_U : x ∉ U := hxEU.1.2
    have hx_not_mem_IU : x ∉ I \ U := hxEU.2
    have hx_not_mem_I : x ∉ I := by
      intro hxI
      exact hxEU.2 ⟨hxI, hx_not_mem_U⟩
    have hx_ground₂ : x ∈ M₂.E := by rwa [← hE]
    have hx_insert_indep : M₂.Indep (insert x (I \ U)) := by
      refine (M₂.indep_iff_eRk_eq_encard_of_finite (I := insert x (I \ U)) (by toFinite_tac)).2 ?_
      simpa [Set.encard_insert_of_notMem hx_not_mem_IU, hI_diff_indep.eRk_eq_encard] using hxrank
    have hx_not_sink : ¬ M₂.Indep (insert x I) := by
      intro hxsink
      exact hx_not_mem_U (hU.sinks_subset ⟨hx_not_mem_I, hxsink⟩)
    have hx_closure : x ∈ M₂.closure I := by
      by_contra hx_not_closure
      exact hx_not_sink <|
        (hI.2.insert_indep_iff_of_notMem hx_not_mem_I).2 ⟨hx_ground₂, hx_not_closure⟩
    have hx_not_closure_diff : x ∉ M₂.closure (I \ U) := by
      have htmp := hx_insert_indep
      rw [hI_diff_indep.insert_indep_iff_of_notMem hx_not_mem_IU] at htmp
      exact htmp.2
    have hfund : M₂.IsCircuit (M₂.fundCircuit x I) := hI.2.fundCircuit_isCircuit hx_closure hx_not_mem_I
    obtain ⟨y, hyDiff, hyU⟩ : ∃ y, y ∈ M₂.fundCircuit x I \ {x} ∧ y ∈ U := by
      by_contra hnone
      have hallDiff : M₂.fundCircuit x I \ {x} ⊆ I \ U := by
        intro y hy
        refine ⟨?_, ?_⟩
        · rw [M₂.fundCircuit_diff_eq_inter hx_not_mem_I] at hy
          exact hy.2
        · by_contra hyU
          exact hnone ⟨y, hy, hyU⟩
      exact hx_not_closure_diff <|
        M₂.closure_subset_closure hallDiff (hfund.mem_closure_diff_singleton_of_mem (M₂.mem_fundCircuit x I))
    have hyFund : y ∈ M₂.fundCircuit x I := hyDiff.1
    have hy_mem_I : y ∈ I := by
      rw [M₂.fundCircuit_diff_eq_inter hx_not_mem_I] at hyDiff
      exact hyDiff.2
    have hy_ne : y ≠ x := by simpa using hyDiff.2
    have hy_step' : M₂.Indep (insert x I \ {y}) := (hI.2.mem_fundCircuit_iff hx_closure hx_not_mem_I).1 hyFund
    have hy_step : LeftArc M₂ I y x := by
      dsimp [LeftArc]
      simpa [insert_diff_singleton_comm hy_ne.symm, hx_not_mem_I] using hy_step'
    exact hx_not_mem_U (hU.right_closed hx_not_mem_I hy_mem_I hy_step hyU)
  · have hsubset : I \ U ⊆ M₁.E \ U := by
      intro z hz
      exact ⟨hI.1.subset_ground hz.1, hz.2⟩
    exact hI_diff_indep.encard_le_eRk_of_subset hsubset

/-- The reachable-set certificate from Edmonds' algorithm proves maximality of the current
common independent set. -/
theorem optimal_of_certificate
    (hE : SameGround M₁ M₂) (hI : CommonIndep M₁ M₂ I)
    (hU : TerminalCertificate M₁ M₂ I U) :
    ∀ ⦃J⦄, CommonIndep M₁ M₂ J → J.encard ≤ I.encard := by
  intro J hJ
  have hleft := left_rank_eq_of_certificate hE hI hU
  have hright := right_rank_eq_of_certificate hE hI hU
  have hJ_left : M₁.Indep (J ∩ U) := hJ.1.subset inter_subset_left
  have hJ_right : M₂.Indep (J ∩ (M₁.E \ U)) := hJ.2.subset inter_subset_left
  have hJ_partition : J = (J ∩ U) ∪ (J ∩ (M₁.E \ U)) := by
    ext z
    constructor
    · intro hzJ
      by_cases hzU : z ∈ U
      · exact Or.inl ⟨hzJ, hzU⟩
      · exact Or.inr ⟨hzJ, hJ.1.subset_ground hzJ, hzU⟩
    · intro hz
      exact hz.elim (fun hzL ↦ hzL.1) (fun hzR ↦ hzR.1)
  have hJ_disj : Disjoint (J ∩ U) (J ∩ (M₁.E \ U)) := by
    refine disjoint_left.2 ?_
    intro z hzL hzR
    exact hzR.2.2 hzL.2
  calc
    J.encard = ((J ∩ U) ∪ (J ∩ (M₁.E \ U))).encard := congrArg Set.encard hJ_partition
    _ = (J ∩ U).encard + (J ∩ (M₁.E \ U)).encard := by rw [Set.encard_union_eq hJ_disj]
    _ ≤ M₁.eRk U + M₂.eRk (M₁.E \ U) := by
      gcongr
      · exact hJ_left.encard_le_eRk_of_subset inter_subset_right
      · exact hJ_right.encard_le_eRk_of_subset inter_subset_right
    _ = (I ∩ U).encard + M₂.eRk (M₁.E \ U) := by rw [hleft]
    _ = (I ∩ U).encard + (I \ U).encard := by rw [hright]
    _ = I.encard := by
      simpa [add_comm] using Set.encard_diff_add_encard_of_subset
        (s := I ∩ U) (t := I) inter_subset_left

/-- If no source can reach a sink in the exchange graph, the reachable set is a terminal
certificate. -/
theorem reachable_certificate
    (hNo : Disjoint (SourceSet M₁ I) (ReachableToSink M₁ M₂ I)) :
    TerminalCertificate M₁ M₂ I (ReachableToSink M₁ M₂ I) := by
  refine ⟨?_, ?_, ?_, hNo⟩
  · intro x hx
    exact ⟨x, hx, Relation.ReflTransGen.refl⟩
  · intro y x hyI hxI hleft hxReach
    rcases hxReach with ⟨z, hzSink, hxz⟩
    exact ⟨z, hzSink, Relation.ReflTransGen.head (Or.inl ⟨hyI, by exact fun h => hxI (h ▸ hyI), hxI, hleft⟩) hxz⟩
  · intro x y hxI hyI hright hyReach
    rcases hyReach with ⟨z, hzSink, hyz⟩
    exact ⟨z, hzSink,
      Relation.ReflTransGen.head (Or.inr ⟨hxI, by exact fun h => hxI (h ▸ hyI), hyI, hright⟩) hyz⟩

/-- Edmonds' terminal criterion: if no source reaches a sink in the exchange graph, then the
current common independent set is maximum. -/
theorem optimal_of_noAugmentingPath
    (hE : SameGround M₁ M₂) (hI : CommonIndep M₁ M₂ I)
    (hNo : Terminal M₁ M₂ I) :
    ∀ ⦃J⦄, CommonIndep M₁ M₂ J → J.encard ≤ I.encard :=
  optimal_of_certificate hE hI (reachable_certificate hNo)

/-- End-to-end abstract correctness: any run that repeatedly augments along certified
no-shortcut paths and stops at Edmonds' terminal condition ends in an optimal common
independent set. -/
theorem run_correct {I₀ I : Set α}
    (hE : SameGround M₁ M₂) (h₀ : CommonIndep M₁ M₂ I₀)
    (hRun : Run M₁ M₂ I₀ I) (hTerm : Terminal M₁ M₂ I) :
    ∀ ⦃J⦄, CommonIndep M₁ M₂ J → J.encard ≤ I.encard := by
  exact optimal_of_noAugmentingPath hE (commonIndep_of_run h₀ hRun) hTerm

/-- Any certified augmentation run that has no outgoing augmentation step ends at an optimal
common independent set. -/
theorem run_correct_of_maximal {I₀ I : Set α}
    (hE : SameGround M₁ M₂) (h₀ : CommonIndep M₁ M₂ I₀)
    (hRun : Run M₁ M₂ I₀ I) (hNo : ¬ ∃ J, AugmentStep M₁ M₂ I J) :
    ∀ ⦃J⦄, CommonIndep M₁ M₂ J → J.encard ≤ I.encard := by
  exact run_correct hE h₀ hRun (terminal_of_no_augmentStep hNo)

/-- Starting from any state, some certified augmentation run reaches a terminal exchange-graph
condition. -/
theorem exists_terminal_run {I : Set α} :
    ∃ J, Run M₁ M₂ I J ∧ Terminal M₁ M₂ J := by
  let C : Set α → Prop := fun S => ∃ J, Run M₁ M₂ S J ∧ Terminal M₁ M₂ J
  change C I
  have hacc : Acc (flip (AugmentStep M₁ M₂)) I := augmentStep_wf.apply I
  refine Acc.recOn hacc ?_
  intro S _ ih
  change C S
  by_cases hTerm : Terminal M₁ M₂ S
  · exact ⟨S, Relation.ReflTransGen.refl, hTerm⟩
  · rcases exists_augmentStep_of_nonterminal hTerm with ⟨T, hStep⟩
    rcases ih T hStep with ⟨J, hRun, hJterm⟩
    exact ⟨J, Relation.ReflTransGen.head hStep hRun, hJterm⟩

/-- Abstract Edmonds correctness: from any common independent set, some certified augmenting run
terminates at an optimal common independent set. -/
theorem exists_optimal_terminal_run {I : Set α}
    (hE : SameGround M₁ M₂) (hI : CommonIndep M₁ M₂ I) :
    ∃ J, Run M₁ M₂ I J ∧ Terminal M₁ M₂ J ∧
      ∀ ⦃K⦄, CommonIndep M₁ M₂ K → K.encard ≤ J.encard := by
  rcases exists_terminal_run (M₁ := M₁) (M₂ := M₂) (I := I) with ⟨J, hRun, hTerm⟩
  exact ⟨J, hRun, hTerm, run_correct hE hI hRun hTerm⟩

end TerminalOptimality

/-- Data for the smallest nontrivial augmenting path in Edmonds' algorithm:
`x₀ → y → x₁`, where `x₀` is a source for `M₁`, `x₁` is a sink for `M₂`,
and the two diagonal exchanges are valid. -/
structure LengthOnePath (M₁ M₂ : Matroid α) (I : Set α) (y x₀ x₁ : α) : Prop where
  y_mem : y ∈ I
  x₀_not_mem : x₀ ∉ I
  x₁_not_mem : x₁ ∉ I
  x_ne : x₀ ≠ x₁
  left_source : M₁.Indep (insert x₀ I)
  left_step : M₁.Indep (insert x₁ (I \ {y}))
  left_internal_span : x₁ ∈ M₁.closure I
  right_step : M₂.Indep (insert x₀ (I \ {y}))
  right_sink : M₂.Indep (insert x₁ I)
  right_internal_span : x₀ ∈ M₂.closure I

/-- Soundness of the smallest nontrivial augmenting step in Edmonds' algorithm. -/
theorem LengthOnePath.commonIndep_augment
    (hI : CommonIndep M₁ M₂ I) (P : LengthOnePath M₁ M₂ I y x₀ x₁) :
    CommonIndep M₁ M₂ (augmentLengthOne I y x₀ x₁) := by
  constructor
  · have hsource_not_closure : x₀ ∉ M₁.closure I := by
      have hsrc := P.left_source
      rw [hI.1.insert_indep_iff_of_notMem P.x₀_not_mem] at hsrc
      exact hsrc.2
    have hstep_subset : insert x₁ (I \ {y}) ⊆ M₁.closure I := by
      refine insert_subset P.left_internal_span ?_
      exact diff_subset.trans (M₁.subset_closure I hI.1.subset_ground)
    have hsource_not_closure_step : x₀ ∉ M₁.closure (insert x₁ (I \ {y})) :=
      fun hx => hsource_not_closure <| by
        simpa [M₁.closure_closure I] using M₁.closure_subset_closure hstep_subset hx
    have hsource_not_mem_step : x₀ ∉ insert x₁ (I \ {y}) := by
      simp [P.x_ne, P.x₀_not_mem]
    rw [augmentLengthOne]
    rw [P.left_step.insert_indep_iff_of_notMem hsource_not_mem_step]
    exact ⟨P.left_source.subset_ground (by simp), hsource_not_closure_step⟩
  · have hsink_not_closure : x₁ ∉ M₂.closure I := by
      have hsink := P.right_sink
      rw [hI.2.insert_indep_iff_of_notMem P.x₁_not_mem] at hsink
      exact hsink.2
    have hstep_subset : insert x₀ (I \ {y}) ⊆ M₂.closure I := by
      refine insert_subset P.right_internal_span ?_
      exact diff_subset.trans (M₂.subset_closure I hI.2.subset_ground)
    have hsink_not_closure_step : x₁ ∉ M₂.closure (insert x₀ (I \ {y})) :=
      fun hx => hsink_not_closure <| by
        simpa [M₂.closure_closure I] using M₂.closure_subset_closure hstep_subset hx
    have hsink_not_mem_step : x₁ ∉ insert x₀ (I \ {y}) := by
      simp [P.x_ne.symm, P.x₁_not_mem]
    rw [augmentLengthOne]
    rw [insert_comm, P.right_step.insert_indep_iff_of_notMem hsink_not_mem_step]
    exact ⟨P.right_sink.subset_ground (by simp), hsink_not_closure_step⟩

section Cardinality

variable [Finite α]

/-- A length-one augmenting step increases the cardinality of the common independent set by one. -/
theorem LengthOnePath.ncard_augment
    (P : LengthOnePath M₁ M₂ I y x₀ x₁) :
    (augmentLengthOne I y x₀ x₁).ncard = I.ncard + 1 := by
  classical
  rw [augmentLengthOne]
  have hy_diff : y ∉ I \ {y} := by simp
  have hx₁_diff : x₁ ∉ I \ {y} := by
    intro hx
    exact P.x₁_not_mem hx.1
  have hx₀_mid : x₀ ∉ insert x₁ (I \ {y}) := by
    simp [P.x_ne, P.x₀_not_mem]
  rw [Set.ncard_insert_of_notMem hx₀_mid, Set.ncard_insert_of_notMem hx₁_diff,
    Set.ncard_diff_singleton_of_mem P.y_mem]
  have hycard := Set.ncard_diff_singleton_add_one (s := I) P.y_mem
  omega

end Cardinality

end Edmonds

end Matroid
