# Cycle 242 Results

## Worked on
Theorem 301A rooted-tree representation upgrade in the nested unary Case D order-5 boundary:
- `BTree.singleton_node_recover_of_childrenBag_eq`
- `BTree.pair_node_recover_of_childrenBag_eq`
- `satisfiesTreeCondition_order_five_via_via_bushy3_canonical`
- `satisfiesTreeCondition_order_five_via_via_chain3_canonical`

## Approach
Audited the live theorem-local exact-list reconstruction points in `OrderConditions.lean` and the existing order-3/order-4/order-5 witness APIs in `RootedTree.lean`.

Added two narrow rooted-tree-side public recovery lemmas that package the singleton and pair exact-node recovery from `childrenBag` equalities. Then rewrote both nested unary Case D canonical wrappers to consume those public lemmas instead of carrying local `show ∃ ... ∧ d = .node [...]` reconstruction blocks.

## Result
SUCCESS.

Visible Lean progress landed in both required Lean files:
- `OpenMath/RootedTree.lean` now exposes public recovery lemmas for singleton and pair node reconstruction from bag equality.
- `OpenMath/OrderConditions.lean` no longer performs theorem-local exact-list reconstruction in either nested unary Case D canonical wrapper; both wrappers now call the rooted-tree recovery API.

Verification:
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/RootedTree.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderConditions.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build OpenMath.RootedTree OpenMath.OrderConditions`

All passed. Existing unrelated linter warnings in `OrderConditions.lean` remain.

## Dead ends
Tried a stronger bag-first helper that attempted to prove a top-level equality
`(BTree.node [c]).childrenBag = ...`
directly from the nested `hcBag` / `hdBag` hypotheses. That was too strong: `c.childrenBag = (BTree.node [d]).childrenBag` does not imply `c = .node [d]`. Replaced that with narrower public recovery lemmas that expose the exact node equality only where it is actually needed.

## Discovery
The real compatibility boundary was not the public `OrderFiveCaseDWitness` payload itself; it was the absence of a rooted-tree-side public theorem that converts a bag-equality against a canonical singleton/pair node into an exact `.node [...]` presentation. Once that API existed, the theorem-side wrappers became a direct refactor.

## Suggested next approach
Look for any remaining theorem-side local `show ∃ ... ∧ _ = .node [...]` compatibility blocks adjacent to the order-5 Case D dispatchers and replace them with public rooted-tree recovery lemmas, but keep the scope narrow in the same style as this cycle.

## Aristotle
Per the cycle 242 planner note and `.prover-state/strategy.md`, I did not submit a fresh Aristotle batch this cycle because there were no completed results ready for incorporation and the strategy explicitly said not to start a fresh batch.
