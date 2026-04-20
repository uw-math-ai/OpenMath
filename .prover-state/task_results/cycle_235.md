# Cycle 235 Results

## Worked on
Theorem 301A bag-first migration for the remaining Case D theorem-side order-4 normalization:
- added a public order-4 recovery theorem in `OpenMath/RootedTree.lean`
- refactored `satisfiesTreeCondition_order_five_caseD_of_orderFourBagWitness` in `OpenMath/OrderConditions.lean` to consume that API in the `.single3` branch

## Approach
Inspected the live bag witness API around `BTree.OrderFourBagWitness`, `BTree.order_four_bag_witness`, and `BTree.order_three_bag_witness_recover`.

Added `BTree.order_four_bag_witness_recover` as a public rooted-tree theorem with a witness-dependent return type:
- `bushy4` recovers a canonical ordered triple of order-1 children
- `mixed4` recovers a canonical ordered pair with orders `(1,2)` or `(2,1)`
- `single3` recovers canonical data directly for the unique child `d`, splitting into
  - `d = .node [e]` with `e.order = 2`, or
  - `d = .node [e₁, e₂]` with `e₁.order = 1` and `e₂.order = 1`

Then simplified the `.single3` branch of
`satisfiesTreeCondition_order_five_caseD_of_orderFourBagWitness`
to call `BTree.order_four_bag_witness_recover` instead of doing local:
- singleton-child recovery
- pair-child recovery
- order arithmetic for the recovered order-3 child shape

## Result
SUCCESS

Visible Lean-code progress:
- theorem-side Case D `.single3` no longer calls
  `BTree.singleton_children_eq_of_childrenBag_eq`
- theorem-side Case D `.single3` no longer calls
  `BTree.pair_children_exists_of_childrenBag_eq`
- theorem-side Case D `.single3` no longer performs local order arithmetic to force the bushy order-3 child into `(1,1)`

## Dead ends
The first version of `order_four_bag_witness_recover` returned one coarse four-way disjunction for all witness constructors. That compiled in `RootedTree.lean`, but it interacted poorly with dependent elimination in `OrderConditions.lean`.

The fix was to keep the same public theorem name but make the return type depend on the `OrderFourBagWitness` constructor, so the `.single3` branch receives only the two relevant canonical child-shape alternatives.

## Discovery
For this boundary, the useful public API is not just “order-4 tree has one of several shapes”; it needs to expose shape data at the same dependency level as the witness constructor. In particular, the `.single3` consumer wants direct recovery information about the witness child `d`, not another existential wrapper around the outer singleton node.

## Suggested next approach
Continue the bag-first migration by checking whether the remaining Case D consumers can also be phrased against witness-dependent recovery theorems, so `OrderConditions.lean` keeps only dispatcher logic and no representation recovery.

## Aristotle
No Aristotle submissions were made this cycle.

Reason:
- the cycle strategy explicitly said there were no completed Aristotle results ready for incorporation
- the cycle strategy explicitly said not to submit a fresh Aristotle batch at the start of the cycle
- this refactor did not require introducing live sorrys or stopping at a proof blocker

## Verification
Ran:

```bash
export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH
lake env lean OpenMath/RootedTree.lean
lake env lean OpenMath/OrderConditions.lean
lake build OpenMath.RootedTree OpenMath.OrderConditions
```
