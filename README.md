# lean-combinatorial-optimization

Lean formalizations of combinatorial optimization arguments and algorithms.

## Projects

- `matroid_intersection/`: a Lean 4 development around Edmonds' augmenting-path proof for matroid
  intersection

## Build

Each project is currently self-contained. For the matroid intersection development:

```bash
cd matroid_intersection
lake build Matroid
```
