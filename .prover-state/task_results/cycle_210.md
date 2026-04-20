# Cycle 210 Results

## Worked on
- `OpenMath/RootedTree.lean`
- `OpenMath/OrderConditions.lean`
- order-5 three-child `{1,1,2}` / `{1,2,1}` / `{2,1,1}` normalization boundary

## Approach
- Confirmed there were no completed Aristotle results ready for incorporation at cycle start.
- Read the existing `childrenBag` transport API in `RootedTree.lean` and the order-5 canonical transport helpers in `OrderConditions.lean`.
- Added a new bag-facing transport lemma for a missing three-child permutation pattern:
  - `BTree.node_childrenBag_eq_rotate_right`
- Added a canonical elementary-weight transport lemma in `OrderConditions.lean`:
  - `ew_of_order_five_3child_eq_of_childrenBag_eq`
- Refactored the ordered `{1,2,1}` and `{2,1,1}` elementary-weight branches to route through the canonical `{1,1,2}` branch via `childrenBag` transport instead of separate ordered `simp`/`ring` proofs.

## Result
- SUCCESS
- `RootedTree.lean` now exposes a right-rotation bag transport for three-child nodes.
- `OrderConditions.lean` now has one canonical bag-transport proof for the order-5 three-child elementary-weight family.
- The ordered normalization scripts removed/simplified were:
  - the direct expansion proof in `ew_of_order_five_121`
  - the direct expansion proof in `ew_of_order_five_211`
- `ew_of_order_five_121` now uses `BTree.node_childrenBag_eq_rotate_right`.
- `ew_of_order_five_211` now uses the existing `BTree.node_childrenBag_eq_rotate_left`.

## Dead ends
- `lake env lean OpenMath/OrderConditions.lean` initially failed to see `node_childrenBag_eq_rotate_right` because the imported `RootedTree.olean` was stale. Rebuilding `OpenMath.RootedTree` fixed that.
- The Aristotle scratch batch did not produce anything worth incorporating into the in-repo proofs:
  - `bag_rotate_right.lean` finished, but used a nonexistent helper (`BTree.childrenBag_perm`) in the returned proof.
  - `ew_3child_transport.lean` finished, but depended on hard-coded order-1/order-2 shape lemmas rather than the in-repo bag-transport path.
  - `ew_121_via_bag.lean` finished with errors after reconstructing ad hoc infrastructure outside the project API.
  - `treecond_3child_canonical.lean` finished, but rebuilt local infrastructure instead of improving the existing proof.
  - `ew_211_via_bag.lean` was still `IN_PROGRESS` at the single post-wait check, so it was not polled again.

## Discovery
- `lake env lean <file>` checks source files, but dependent files can still read stale imported `.olean` artifacts; for an import-sensitive refactor, rebuilding the changed dependency first is safer.
- The order-5 three-child family already had canonical bag transport at the tree-condition level, but not yet at the lower `elementaryWeight` level. Adding that lower transport closed a real remaining ordered-witness boundary.

## Suggested next approach
- Push the same pattern one step further by extracting a reusable canonical bag-transport helper for the order-5 three-child family at the theorem level, so `satisfiesTreeCondition_order_five_3child_canonical` can rely on the new lower-level transport lemma directly.
- After that, target another remaining ordered family with nested unary wrappers, where local proofs still manually rebuild unary transport rather than consuming a single bag-native helper.

## Aristotle batch
- No ready Aristotle results were available at cycle start.
- Submitted 5 scratch jobs after the local refactor setup:
  - `9c74b3ff-f97b-4127-aec8-3a61cc18a291` `bag_rotate_right.lean` → `COMPLETE`
  - `2decdcf8-a433-469b-868a-d7dcae59ec2c` `ew_3child_transport.lean` → `COMPLETE`
  - `53e35c39-69b4-4366-a717-10ec1c9b3181` `ew_121_via_bag.lean` → `COMPLETE_WITH_ERRORS`
  - `638f3084-6493-4762-9aff-a7747cfdf5e5` `ew_211_via_bag.lean` → `IN_PROGRESS`
  - `66a7ce8d-281d-43e8-b954-3e07ae3fbfe3` `treecond_3child_canonical.lean` → `COMPLETE`
- Waited 30 minutes once, then refreshed the batch once.
- Incorporated none of the returned proofs because they were either incompatible with the in-repo API, lower-quality than the landed proofs, or still unfinished.

## Verification
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/RootedTree.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build OpenMath.RootedTree`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderConditions.lean`
