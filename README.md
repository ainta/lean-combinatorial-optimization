# lean-combinatorial-optimization

Lean formalizations of combinatorial optimization arguments and algorithms.

## Projects

- `matroid_intersection/`: a Lean 4 development around Edmonds' augmenting-path proof for matroid
  intersection
- `max_flow_min_cut/`: a Lean 4 development of the max-flow min-cut theorem

## Build

Each project is currently self-contained. For the matroid intersection development:

```bash
cd matroid_intersection
lake build Matroid
```

For the max-flow / min-cut development:

```bash
cd max_flow_min_cut
lake build MaxFlowMinCut
```
