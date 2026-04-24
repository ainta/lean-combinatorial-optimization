import MaxFlowMinCut.Residual

/-!
# Augmenting a flow along a residual path

The pointwise update operations on flow values (`addEntry`, `subEntry`) and the per-vertex
balance bookkeeping (`augOut`, `augIn`, `augBal`), assembled into `augmentVal`: the new value
function obtained by traversing a residual path and incrementing forward edges / decrementing the
underlying capacities of backward edges. The headline result is
`exists_better_flow_of_residualPath`: any residual `source → sink` path can be turned into a
`Flow` with strictly larger value.
-/

open scoped BigOperators

namespace MaxFlowMinCut

section Network

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Flow

variable {N : Network (V := V)}

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
                exact hy ((Quiver.Path.mem_vertices_cons p (ResidualEdge.forward h)).2
                  (Or.inr hxy'.2))
          simp [augmentVal, addEntry]
          rw [if_neg (by simpa using hne), ih']
      | backward h =>
          have hne : ¬ (x = (p.cons (ResidualEdge.backward h)).end ∧ y = p.end) := by
            intro hxy'
            cases hxy with
            | inl hx =>
                exact hx ((Quiver.Path.mem_vertices_cons p (ResidualEdge.backward h)).2
                  (Or.inr hxy'.1))
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
                      simp [hxp]
                    · simp
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
                      simp [hxp]
                      omega
                    · simp
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

end Flow

end Network

end MaxFlowMinCut
