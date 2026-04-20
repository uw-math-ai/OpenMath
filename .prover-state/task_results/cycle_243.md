# Cycle 243 Results

## Worked on
Theorem 301A order-5 Case C first-level `{1, bushy-3}` and `{1, chain-3}` representation boundary cleanup in `OpenMath/OrderConditions.lean`.

## Approach
Audited the live boundary around:
- `BTree.OrderThreeBagWitness`
- `BTree.order_three_bag_witness`
- `BTree.order_three_bag_witness_recover`
- `BTree.OrderFiveCaseCWitness`
- `BTree.order_five_caseC_witness`
- `satisfiesTreeCondition_order_five_1_bushy3`
- `satisfiesTreeCondition_order_five_1_chain3`
- `satisfiesTreeCondition_order_five_bushy3_canonical`
- `satisfiesTreeCondition_order_five_chain3_canonical`

Then refactored the two first-level family theorems so their hypotheses are bag-first:
- `satisfiesTreeCondition_order_five_1_bushy3` now takes `c₂.childrenBag = (BTree.node [d₁, d₂]).childrenBag`
- `satisfiesTreeCondition_order_five_1_chain3` now takes `c₂.childrenBag = (BTree.node [d]).childrenBag`

Kept the reconstruction local inside those family theorems only, so the canonical consumers could be rewritten to stop case-splitting on `c₁`/`c₂` just to rebuild literal `.node [...]` values.

For the swapped orientation, used `satisfiesTreeCondition_eq_of_childrenBag_eq` with `BTree.node_childrenBag_eq_swap` and then invoked the new bag-first family theorem on the swapped tree.

## Result
SUCCESS.

Visible Lean progress:
- `satisfiesTreeCondition_order_five_1_bushy3` no longer uses an exact-list existential theorem statement.
- `satisfiesTreeCondition_order_five_1_chain3` no longer uses an exact-list existential theorem statement.
- `satisfiesTreeCondition_order_five_bushy3_canonical` no longer reconstructs exact child lists locally.
- `satisfiesTreeCondition_order_five_chain3_canonical` no longer reconstructs exact child lists locally.

`OpenMath/RootedTree.lean` did not need changes.

## Dead ends
Initially tried proving the new bag-first family theorems by calling the existing `..._eq_of_childrenBag_eq` transport lemmas directly. That failed because those transport lemmas are defined later in the file and still require exact node equalities in their hypotheses. I moved the exact-node recovery into the family theorems instead, which kept the consumer-facing boundary bag-first and compiled cleanly.

## Discovery
The remaining representation debt was exactly at the theorem boundary, not in the public rooted-tree witness layer. No new `RootedTree` helper was needed once the canonical consumers were rewritten to use top-level swap transport plus the bag-first family theorems.

## Suggested next approach
Continue the same cleanup pattern only if more theorem-local exact-list boundaries remain adjacent to Theorem 301A:
- change the boundary theorem statement to bag-first
- keep any unavoidable exact-node recovery inside that boundary theorem
- remove local reconstruction from the immediate canonical consumer by combining the bag-first theorem with top-level bag-equality transport

## Aristotle
No Aristotle submission was made this cycle. The planner strategy for cycle 243 explicitly said there were no completed Aristotle results ready for incorporation and to not start by submitting a fresh batch this cycle, so I followed that constraint.

## Verification
Ran:
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/RootedTree.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderConditions.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build OpenMath.RootedTree OpenMath.OrderConditions`

All succeeded. `OpenMath/OrderConditions.lean` still reports the pre-existing linter warnings/info messages already present in this area.
