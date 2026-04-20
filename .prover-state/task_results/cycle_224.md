# Cycle 224 Results

## Worked on
`OpenMath/RootedTree.lean` order-3 and order-4 compatibility wrappers:
- `order_three_witness_nonempty`
- `order_three_witness`
- `order_three_cases`
- `order_four_witness_nonempty`
- `order_four_witness`
- `order_four_cases`

## Approach
Refactored the old ordered-list compatibility witnesses to derive from the existing bag-first witnesses instead of re-running the old list-length/order-sum classifier.

Added narrow private helper lemmas in `RootedTree.lean` to recover:
- exact singleton children from singleton bag equality,
- existence of an ordered pair from two-child bag equality,
- existence of an ordered triple from three-child bag equality,
- local node-order transport from children-bag equality,
- the derived `t.order = 3` fact from `OrderThreeBagWitness`.

Then rewrote:
- `order_three_witness_nonempty` to case on `order_three_bag_witness t ht`,
- `order_four_witness_nonempty` to case on `order_four_bag_witness t ht`,

and reconstructed only the minimal ordered fallback data needed by the old public compatibility witness types.

## Result
SUCCESS.

`OpenMath/RootedTree.lean` now treats the ordered compatibility layer as a thin shim over `OrderThreeBagWitness` and `OrderFourBagWitness`.

`OpenMath/OrderConditions.lean` compiled unchanged against the refactored wrapper boundary.

Verification run:
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/RootedTree.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderConditions.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build OpenMath.RootedTree OpenMath.OrderConditions`

## Dead ends
Initial wrapper proofs referenced `order_eq_of_childrenBag_eq` and `order_pos` before those later file definitions were in scope. Replaced that with a local private node-order transport proof using `List.Perm.foldr_eq` and local positivity proofs by case analysis on trees.

## Discovery
The remaining compatibility layer can be kept local to `RootedTree.lean` with only three small bag-to-list recovery helpers and one local order-transport lemma; no new public API was needed.

The active theorem consumer in `OrderConditions.lean` is already genuinely bag-first and did not need any edits.

## Suggested next approach
Continue shrinking the old ordered fallback boundary by targeting the next remaining compatibility-only consumers, if any, while preserving the current public API until the bag-first interface is fully dominant.

## Aristotle
No Aristotle batch was submitted this cycle.

Reason: the planner for cycle 224 explicitly said not to submit a new batch unless this cycle first created a genuinely new hard subgoal beyond local witness/plumbing refactors. This cycle stayed within the intended wrapper-refactor scope and did not introduce a new hard formal proof subproblem.
