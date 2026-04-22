import Matroid.CommonIndep

/-!
# Edmonds' exchange graph

The directed exchange graph used by Edmonds' matroid-intersection algorithm, together with the
source/sink sets, the terminal-certificate structure, and the reachability-based terminal
condition. The graph is built from two matroids `M₁ M₂` and a current common independent set `I`.

The same set `{x ∉ I | M.Indep (insert x I)}` plays two distinct roles in the algorithm: as the
sources of `M₁` and as the sinks of `M₂`. We expose it once as `IndepExtension`, and keep
`SourceSet`/`SinkSet` as semantic abbreviations.
-/

open Set

namespace Matroid.Intersection

variable {α : Type*} {M₁ M₂ : Matroid α} {I : Set α}

/-- The two matroids in a matroid-intersection instance share the same ground set. -/
def SameGround (M₁ M₂ : Matroid α) : Prop :=
  M₁.E = M₂.E

/-- The result of augmenting `I` along a finite alternating path with outside vertices `x`
and inside vertices `y`. -/
def augmentPath (I : Set α) {n : ℕ} (x : Fin (n + 1) → α) (y : Fin n → α) : Set α :=
  (I \ Set.range y) ∪ Set.range x

/-- The outside vertex preceding step `i` along an alternating path. -/
def xPrev {n : ℕ} (x : Fin (n + 1) → α) (i : Fin n) : α :=
  x i.castSucc

/-- The outside vertex following step `i` along an alternating path. -/
def xNext {n : ℕ} (x : Fin (n + 1) → α) (i : Fin n) : α :=
  x i.succ

/-- The final outside vertex of an alternating path. -/
def xLast {n : ℕ} (x : Fin (n + 1) → α) : α :=
  x (Fin.last n)

/-- The left exchange relation `y → x` in the exchange graph of `M` at `I`. -/
def LeftArc (M : Matroid α) (I : Set α) (y x : α) : Prop :=
  M.Indep (insert x (I \ {y}))

/-- The set of elements outside `I` whose insertion preserves `M`-independence.
Plays two roles in Edmonds' algorithm — see `SourceSet` and `SinkSet`. -/
def IndepExtension (M : Matroid α) (I : Set α) : Set α :=
  {x | x ∉ I ∧ M.Indep (insert x I)}

/-- The source set for the first matroid in Edmonds' exchange graph. -/
abbrev SourceSet (M : Matroid α) (I : Set α) : Set α := IndepExtension M I

/-- The sink set for the second matroid in Edmonds' exchange graph. -/
abbrev SinkSet (M : Matroid α) (I : Set α) : Set α := IndepExtension M I

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

end Matroid.Intersection
