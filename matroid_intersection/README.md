# matroid_intersection

Toy Lean 4 project for formalizing Edmonds' augmenting-path proof of matroid intersection with mathlib's matroid library.

## Current scope

The current module is [`Matroid/Intersection.lean`](./Matroid/Intersection.lean).

It now formalizes:

- `Matroid.CommonIndep`: common independence for two matroids
- `Matroid.Intersection.Terminal`: Edmonds' exchange-graph terminal condition
- `exists_simpleAugPath_of_not_terminal`: nonterminal states admit an explicit finite augmenting path
- `exists_noShortcutPath_of_not_terminal`: nonterminal states admit a certified no-shortcut path
- `Matroid.Intersection.NoShortcutPath`: a finite no-shortcut augmenting path
- `NoShortcutPath.source_mem_reachableToSink`: such a path really is a source-to-sink exchange-graph witness
- `NoShortcutPath.commonIndep_augment`: augmenting along such a path preserves common independence
- `NoShortcutPath.ncard_augment`: such an augmentation increases cardinality by `1`
- `Matroid.Intersection.AugmentStep` and `Run`: abstract augmentation-step and run semantics
- `terminal_iff_no_augmentStep`: terminal states are exactly the states with no certified augmentation
- `run_correct_of_maximal`: any certified augmentation run that cannot continue ends at a maximum
  common independent set
- `exists_optimal_terminal_run`: some certified augmentation run reaches an optimal terminal state
- `Matroid.Intersection.TerminalCertificate`: the reachable-set certificate used at termination
- `optimal_of_certificate`: the min-max optimality argument from the terminal certificate
- `ReachableToSink`, `reachable_certificate`, and `optimal_of_noAugmentingPath`: the exchange-graph version of the terminal theorem

The development now proves the finite abstract correctness statement: repeated certified
augmentation in the exchange graph terminates, and any maximal certified run ends at a maximum
cardinality common independent set. It still does not formalize a concrete executable search
procedure such as BFS/DFS for finding the next augmenting path witness.

## References

- mathlib matroid API:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Matroid/Basic.html
- Goemans lecture notes on matroid intersection:
  https://math.mit.edu/~goemans/18438F09/lec11.pdf
- Cole Franks lecture notes:
  https://colefranks.github.io/18453/lecturenotes/6-matroid-intersect-notes.pdf
- blog proof outline used to shape the toy formalization:
  https://ainta.github.io/2019-06-17-Matroid-Intersection

## Build

```bash
cd matroid_intersection
lake build Matroid
```
