# Cycle 228 Results

## Worked on
Order-5 rooted-tree infrastructure in `OpenMath/RootedTree.lean` and the reverse branch of `thm_301A_order5` in `OpenMath/OrderConditions.lean`.

## Approach
Mirrored the existing order-3 and order-4 bag-first witness architecture for order 5.
Added `OrderFiveBagWitness`, `order_five_bag_witness_nonempty`, and `order_five_bag_witness`.
Added the minimal helper `four_children_exists_of_childrenBag_eq` for recovering a 4-child list from `childrenBag` equality.
Downgraded `OrderFiveWitness` to a compatibility layer derived from `OrderFiveBagWitness`.
Rewired `thm_301A_order5` reverse direction to case-split on `BTree.OrderFiveBagWitness` and transport to the existing shared case dispatchers through `satisfiesTreeCondition_eq_of_childrenBag_eq`.

## Result
SUCCESS. Order 5 now has a bag-first rooted-tree witness boundary.
`OpenMath/OrderConditions.lean` now consumes `BTree.order_five_bag_witness` in the reverse direction of `thm_301A_order5`.
`OrderFiveWitness` remains only as a derived compatibility wrapper.
No new `sorry`s were introduced.

## Dead ends
`OpenMath/OrderConditions.lean` initially picked up the old `RootedTree` export surface until `lake build OpenMath.RootedTree` refreshed the `.olean`.
The first compatibility proof for the order-5 three-child branch over-simplified the node-order equality; switching to an explicit `omega` proof over the bag-preserved node orders resolved it.

## Discovery
The order-5 migration needed exactly one new rooted-tree recovery helper: `four_children_exists_of_childrenBag_eq`.
The existing theorem-level shared dispatchers for Case B / C / D were already sufficient once the theorem boundary moved to `childrenBag` transport.

## Suggested next approach
Check whether any downstream code still consumes `OrderFiveWitness` directly; if not, the compatibility wrapper may now be removable in a later cleanup cycle.
If further rooted-tree upgrades continue, follow the same pattern: bag-first witness in `RootedTree.lean`, then narrow consumer rewrites via `childrenBag` transport rather than new ordered-list APIs.

## Verification
Passed:
`export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/RootedTree.lean`
`export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build OpenMath.RootedTree`
`export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderConditions.lean`
`export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build OpenMath.OrderConditions`

## Aristotle
No Aristotle submission this cycle. The planner explicitly marked cycle 228 as a rooted-tree representation-upgrade cycle and instructed not to submit a new batch unless real Lean progress uncovered a genuinely new hard blocker. No such blocker appeared.
