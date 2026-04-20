# Cycle 254 Results

## Worked on
`OpenMath/OrderConditions.lean` order-5 theorem-side cleanup for the remaining exact-list staging around:
- `satisfiesTreeCondition_order_five_3child_112`
- `satisfiesTreeCondition_order_five_1_bushy3_exact`
- `satisfiesTreeCondition_order_five_1_chain3_exact`

## Approach
Audited the live order-5 pipeline and checked the theorem boundary in `thm_301A_order5` plus the Case B / Case C dispatchers.

Confirmed that the public consumers are already bag-first / witness-first, so the remaining exact-list theorems were private staging only.

Refactored the file to:
- delete the private exact theorem `satisfiesTreeCondition_order_five_3child_112`
- prove `satisfiesTreeCondition_order_five_3child_eq_of_childrenBag_eq` directly from `childrenBag` transport plus the existing elementary-weight transport
- delete the single-use private exact theorems `satisfiesTreeCondition_order_five_1_bushy3_exact` and `satisfiesTreeCondition_order_five_1_chain3_exact`
- inline the recovered-node proof into `satisfiesTreeCondition_order_five_1_bushy3` and `satisfiesTreeCondition_order_five_1_chain3`

## Result
SUCCESS — removed the remaining theorem-side exact-list staging for the targeted order-5 families without changing the public theorem boundary.

The order-5 theorem boundary in `OrderConditions.lean` remains bag-first / witness-first:
- Case B flows through `OrderFiveCaseBWitness`
- Case C flows through `OrderFiveCaseCWitness`
- Case D flows through `OrderFiveCaseDWitness`
- the only public order-5 theorem is still `thm_301A_order5`

The remaining deeper gap is datatype-level rather than theorem-boundary-level: `BTree` still stores children as an ordered `List`, with bag-first reasoning layered on top via `childrenBag`.

## Dead ends
Did not introduce new `sorry`s or new helper APIs. The cleanup did not require Aristotle, because there was no new hard sublemma or live `sorry` after the audit.

## Discovery
The targeted exact-list lemmas were no longer carrying any public theorem-side obligation. They were only single-use private wrappers around canonical ordered presentations.

The `{1,1,2}` three-child family can be handled directly from density transport plus `ew_of_order_five_3child_eq_of_childrenBag_eq`, so its separate tree-condition exact theorem was redundant.

## Suggested next approach
Treat the theorem-boundary migration for Theorem 301A order 5 as complete.

If future work is needed here, it should target the underlying rooted-tree datatype design: replacing or abstracting over `List`-based child storage, rather than continuing theorem-side bag-transport cleanup.

## Aristotle
No Aristotle jobs were submitted this cycle. The cycle strategy explicitly said not to submit at the start, and this cleanup introduced no new hard sublemma or live `sorry`.

## Verification
Ran:
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/RootedTree.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderConditions.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build`
