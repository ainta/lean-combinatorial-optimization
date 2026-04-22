# robinson_schensted plan

Initial scope: formalize Robinson-Schensted first, not full RSK.

## Placement

This work should live under a new top-level category:

- `algebraic_combinatorics/robinson_schensted/`

It should remain separate from `combinatoric_optimization/`.

## Scope

First milestone:

- input: permutations
- output: a pair of standard Young tableaux of the same shape
- core components: insertion tableau, recording tableau, reverse insertion, bijection

Later milestone:

- generalize to biwords
- then package full Robinson-Schensted-Knuth

## Proposed file layout

- `RS.lean`
- `RS/Tableau.lean`
- `RS/Standard.lean`
- `RS/RowInsert.lean`
- `RS/TableauInsert.lean`
- `RS/RobinsonSchensted.lean`
- `RS/Reverse.lean`
- `RS/Bijection.lean`

## Representation strategy

Use two layers.

- Internal algorithm layer: concrete list-based tableaux.
- External specification layer: `YoungDiagram` and `SemistandardYoungTableau`.

The local mathlib snapshot has `YoungDiagram` and `SemistandardYoungTableau`, but not a native
`StandardYoungTableau` type, so the RS stage will likely need a local standard-tableau wrapper or
subtype.

## Proof order

1. Internal tableau validity and shape extraction.
2. Row insertion and bump lemmas.
3. Tableau insertion preserves tableau invariants.
4. Shape grows by exactly one cell.
5. Iteration over permutations builds `P` and `Q`.
6. Reverse insertion.
7. Forward and reverse algorithms are inverse.

## Main proof risks

- row insertion preserves semistandardness
- reverse insertion is well defined
- internal representation cleanly exports to mathlib tableau objects
