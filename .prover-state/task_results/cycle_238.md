# Cycle 238 Results

## Worked on
Promoted the order-5 Case D singleton-child normalization witness from `OpenMath/OrderConditions.lean` into the public rooted-tree API in `OpenMath/RootedTree.lean`, then refactored the theorem-side Case D dispatcher and reverse branch to consume that public witness.

## Approach
Read the live strategy and audited the existing Case B/C/Case D boundaries first.

Added a new public rooted-tree witness:
- `BTree.OrderFiveCaseDWitness`
- `BTree.order_five_caseD_witness_nonempty`
- `BTree.order_five_caseD_witness`

The new witness is recovered from the existing public order-4 bag witness infrastructure, especially `BTree.order_four_bag_witness` and `BTree.order_four_bag_witness_recover`.

Then removed the theorem-local Case D witness layer and rewrote `order_five_caseD_target`, `order_five_caseD_dispatch_shared`, and the reverse Case D branch of `thm_301A_order5` to use `BTree.OrderFiveCaseDWitness`.

## Result
SUCCESS

Visible Lean-code progress landed:
- new public Case D rooted-tree witness API in `OpenMath/RootedTree.lean`
- deletion of theorem-local `OrderFiveCaseDWitness`
- deletion of theorem-local `OrderFiveCaseD_BushyMixed`
- reverse Case D branch now chooses `BTree.order_five_caseD_witness` and dispatches through the shared theorem-side wrapper

## Dead ends
`lake env lean OpenMath/OrderConditions.lean` initially failed to see the new public symbols from `RootedTree.lean` because the dependency `.olean` was stale. Rebuilding `OpenMath.RootedTree` fixed that cleanly.

## Discovery
The remaining theorem-side Case D logic is now just tableau-specific dispatch; the rooted-tree normalization boundary itself is public and no longer duplicated in `OrderConditions.lean`.

The new public witness can be reconstructed entirely from existing rooted-tree bag witnesses without introducing any tableau-side payload into `RootedTree.lean`.

## Suggested next approach
Continue shrinking theorem-local normalization around Theorem 301A by looking for any remaining tree-shape dispatch that still packages rooted-tree data privately instead of through public `BTree` witnesses.

## Aristotle
No Aristotle batch was submitted this cycle.

Reason:
- the cycle strategy explicitly said not to begin by submitting a fresh Aristotle batch;
- there were no live `sorry`s to batch;
- the Case D migration completed in-repo without a new proof blocker.

## Verification
Ran:

```bash
export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH
lake env lean OpenMath/RootedTree.lean
lake build OpenMath.RootedTree
lake env lean OpenMath/OrderConditions.lean
lake build OpenMath.RootedTree OpenMath.OrderConditions
```
