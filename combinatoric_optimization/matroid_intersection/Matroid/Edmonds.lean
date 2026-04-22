import Matroid.Edmonds.Search
import Matroid.Edmonds.Algorithm

/-!
# Matroid intersection: Edmonds' algorithm layer

Algorithmic / executable layer for matroid intersection. The mathematical theorem layer is in
`Matroid.Intersection`; this module sits on top of it and parameterizes the algorithm by an
abstract search procedure.

- `Matroid.Edmonds.Search` — the `SearchSpec` interface and a noncomputable witness.
- `Matroid.Edmonds.Algorithm` — the iterator and its correctness theorems, including the
  algorithmic form of the matroid-intersection min-max theorem.

Concrete computable instances of `SearchSpec` (e.g. BFS on the exchange graph under
`DecidablePred M.Indep`) live downstream and are out of scope for this module.
-/
