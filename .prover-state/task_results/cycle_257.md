# Cycle 257 Results

## Worked on
Refactored the top-level order-5 rooted-tree classifier boundary away from the
ordered-list payload in `BTree.OrderFiveBagWitness`.

Added a new recovery-first API in `OpenMath/RootedTree.lean`:
- `BTree.OrderFiveRecoveryWitness`
- `BTree.order_five_recovery_witness_nonempty`
- `BTree.order_five_recovery_witness`

Updated `OpenMath/OrderConditions.lean` so the reverse direction of
`thm_301A_order5` now consumes `OrderFiveRecoveryWitness` directly.

## Approach
I first read the cycle strategy and confirmed that the theorem-side remaining
ordered boundary was the `OrderFiveBagWitness` split in `thm_301A_order5`.

I then introduced a recovery-first top-level witness with four constructors:
- `bushy5`, carrying only `t.childrenBag = canonicalBag` and leaf-order facts
- `caseB`, carrying `t.childrenBag = canonicalBag` plus `OrderFiveCaseBWitness`
- `caseC`, carrying `t.childrenBag = canonicalBag` plus `OrderFiveCaseCWitness`
- `caseD`, carrying `t.childrenBag = canonicalBag` plus `OrderFiveCaseDWitness`

For the chooser proof, I reused `order_five_bag_witness` only as temporary
construction scaffolding, immediately promoting each old branch into the new
recovery-first witness.

After that, I rewired the reverse direction of `thm_301A_order5` to:
- destruct `t` as a node
- choose `BTree.order_five_recovery_witness (.node children) heq`
- dispatch Case B/C/D through the existing canonical theorem-side transport
  using the embedded normalized witnesses
- transport back to the original tree only via `childrenBag` equality

Verification commands:

```bash
export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH
lake build OpenMath.RootedTree
lake build OpenMath.OrderConditions
lake env lean OpenMath/RootedTree.lean
lake env lean OpenMath/OrderConditions.lean
lake build
```

## Result
SUCCESS.

`thm_301A_order5` no longer matches on `OrderFiveBagWitness ... children ...` at
the theorem boundary. It now consumes `OrderFiveRecoveryWitness` directly.

No old top-level compatibility names were removed this cycle. The old
`OrderFiveBagWitness` / `order_five_bag_witness` layer remains in
`OpenMath/RootedTree.lean`, but only as internal scaffolding for constructing
the new recovery witness; it is no longer used by the theorem consumer in
`OrderConditions.lean`.

## Dead ends
No structural blocker was hit.

I did not pursue a larger cleanup of `OrderFiveBagWitness` after migrating the
consumer, to keep the cycle narrowly focused on the theorem boundary refactor.

No Aristotle jobs were submitted. The cycle strategy explicitly said not to
poll or submit for this structural refactor unless a genuinely hard new
sublemma or live `sorry` appeared, and that did not happen.

## Discovery
The public order-5 theorem consumer is now recovery-first:
- `thm_301A_order5` depends on `OrderFiveRecoveryWitness`
- the theorem-side B/C/D routing depends on the normalized
  `OrderFiveCaseB/C/DWitness` payloads
- the only remaining ordered-list-sensitive top-level compatibility layer is
  the legacy `OrderFiveBagWitness` chooser inside `RootedTree.lean`

## Suggested next approach
If the planner wants to continue this representation upgrade, the next step is
to either:
- delete `OrderFiveBagWitness` outright by proving
  `order_five_recovery_witness_nonempty` directly, or
- demote it to a clearly internal/private compatibility wrapper once no other
  internal helpers depend on it.
