# lean-algorithms

Lean formalizations of algorithms and their correctness.

## Areas

- [`combinatoric_optimization/`](./combinatoric_optimization) — combinatorial optimization
  - [`matroid_intersection/`](./combinatoric_optimization/matroid_intersection) — Edmonds-style proof of the matroid-intersection min-max theorem, plus an algorithm-correctness layer parameterized by an abstract search procedure
  - [`max_flow_min_cut/`](./combinatoric_optimization/max_flow_min_cut) — Lean 4 development of the max-flow / min-cut theorem
- [`algebraic_combinatorics/`](./algebraic_combinatorics) — algebraic combinatorics
  - [`robinson_schensted/`](./algebraic_combinatorics/robinson_schensted) — Robinson-Schensted correspondence on permutations, packaged as a bijection between nodup words and forward-image tableau-pair states

## Build

Each project is self-contained. For example:

```bash
cd combinatoric_optimization/matroid_intersection
lake build
```

```bash
cd combinatoric_optimization/max_flow_min_cut
lake build
```

```bash
cd algebraic_combinatorics/robinson_schensted
lake build
```
