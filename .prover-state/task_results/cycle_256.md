# Cycle 256 Results

## Worked on
Deleted the dead order-3 / order-4 compatibility wrapper layer from `OpenMath/RootedTree.lean`.

Removed names:
- `OrderThreeBagWitness`
- `order_three_bag_witness_recover`
- `order_three_bag_witness_nonempty`
- `order_three_bag_witness`
- `order_threeBagWitness_order_eq`
- `OrderFourBagWitness`
- `order_four_bag_witness_recover`
- `order_four_bag_witness_nonempty`
- `order_four_bag_witness`
- `order_fourBagWitness_order_eq`

## Approach
First confirmed the wrapper API was dead outside `OpenMath/RootedTree.lean` with:

```bash
rg -n "OrderThreeBagWitness|order_three_bag_witness\\b|OrderFourBagWitness|order_four_bag_witness\\b" OpenMath --glob '!OpenMath/RootedTree.lean'
```

That returned no matches, so I removed the order-3 and order-4 compatibility layer directly from `RootedTree.lean` while leaving the recovery-first API unchanged:
- `OrderThreeRecoveryWitness`
- `order_three_recovery_witness_nonempty`
- `order_three_recovery_witness`
- `OrderFourRecoveryWitness`
- `order_four_recovery_witness_nonempty`
- `order_four_recovery_witness`
- `order_fourRecoveryWitness_order_eq`

I then re-ran a full-tree reference search:

```bash
rg -n "OrderThreeBagWitness|order_three_bag_witness\\b|order_threeBagWitness_order_eq|OrderFourBagWitness|order_four_bag_witness\\b|order_fourBagWitness_order_eq" OpenMath
```

and verified:

```bash
export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH
lake env lean OpenMath/RootedTree.lean
lake env lean OpenMath/OrderConditions.lean
lake build
```

## Result
SUCCESS.

The order-3 / order-4 compatibility wrapper layer was deleted cleanly. After the refactor, no references to the deleted names remained anywhere under `OpenMath`.

`OrderFiveBagWitness` is now the first remaining public classifier in `OpenMath/RootedTree.lean` that still carries raw ordered-list payload via `children : List BTree`.

## Dead ends
No proof-search dead ends this cycle. This was a structural deletion only.

No Aristotle jobs were submitted. The cycle strategy explicitly said not to start with Aristotle triage here, there were no live code `sorry`s, and this cleanup did not introduce new hard sublemmas.

## Discovery
The live low-order classifier path is now recovery-first only for orders 3 and 4. The surviving witness inventory in `RootedTree.lean` is:
- `OrderThreeRecoveryWitness`
- `order_three_recovery_witness`
- `OrderFourRecoveryWitness`
- `order_four_recovery_witness`
- `OrderFiveBagWitness`
- `order_five_bag_witness`

This leaves `OrderFiveBagWitness` as the next obvious representation-upgrade target if the planner wants to continue shrinking the ordered-list compatibility surface.

## Suggested next approach
Target `OrderFiveBagWitness` next and audit whether its theorem consumers can be shifted to a recovery-first witness in the same style as orders 3 and 4, without attempting the full `BTree.node : List BTree → BTree` redesign in one cycle.
