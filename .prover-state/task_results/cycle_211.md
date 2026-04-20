# Cycle 211 Results

## Worked on
- Aristotle triage for ready bundles `66a7ce8d-281d-43e8-b954-3e07ae3fbfe3`, `2decdcf8-a433-469b-868a-d7dcae59ec2c`, `9c74b3ff-f97b-4127-aec8-3a61cc18a291`, then `638f3084-6493-4762-9aff-a7747cfdf5e5` and `53e35c39-69b4-4366-a717-10ec1c9b3181`
- Order-4 mixed-family canonicalization boundary in `OpenMath/OrderConditions.lean`

## Approach
- Inspected the current bag-facing API in `OpenMath/RootedTree.lean` and the existing order-5 transport pattern in `OpenMath/OrderConditions.lean`.
- Compared each required Aristotle bundle against the current in-repo code with one question: does it directly help the live order-4 mixed bag-transport boundary?
- Refactored the order-4 mixed family to match the order-5 pattern:
  one canonical `{1,2}` elementary-weight theorem,
  one density theorem for the canonical witness,
  one bag-transport elementary-weight theorem,
  one bag-transport tree-condition theorem,
  and one canonical wrapper consuming the swap bag equality.

## Result
- SUCCESS: removed the direct ordered `ew_of_order_four_mixed21` branch and replaced the swapped-orientation handling with bag transport.
- Reused existing `RootedTree.lean` lemmas instead of adding new ones:
  `BTree.node_childrenBag_eq_swap`
  `BTree.density_eq_of_childrenBag_eq`
- Simplified the order-4 mixed density boundary:
  `density_of_order_four_mixed` is now the canonical `{1,2}` density theorem only.
- Added new order-4 mixed transport lemmas in `OpenMath/OrderConditions.lean`:
  `ew_of_order_four_mixed_eq_of_childrenBag_eq`
  `density_of_order_four_mixed_eq_of_childrenBag_eq`
  `satisfiesTreeCondition_order_four_mixed_eq_of_childrenBag_eq`
- Updated `satisfiesTreeCondition_order_four_mixed_canonical` to dispatch the swapped case through `childrenBag` equality instead of a separate ordered proof branch.

## Dead ends
- `66a7ce8d-281d-43e8-b954-3e07ae3fbfe3`: redundant with the already-landed order-5 three-child canonical/tree-condition infrastructure; not incorporated.
- `2decdcf8-a433-469b-868a-d7dcae59ec2c`: redundant with the existing order-5 three-child transport lemmas; not incorporated.
- `9c74b3ff-f97b-4127-aec8-3a61cc18a291`: redundant with existing `BTree.node_childrenBag_eq_rotate_right`; not incorporated.
- `638f3084-6493-4762-9aff-a7747cfdf5e5`: order-5-only and structurally redundant with current in-repo canonical/transport lemmas; not incorporated.
- `53e35c39-69b4-4366-a717-10ec1c9b3181`: stale standalone reconstruction of an order-5 orientation proof, not reusable for the live order-4 boundary; not incorporated.

## Discovery
- The repo already had enough bag-facing infrastructure in `RootedTree.lean`; the missing piece for order 4 was local transport structure in `OrderConditions.lean`, not new tree invariants.
- The productive change was to mirror the order-5 pattern exactly and make the canonical theorem the only computational branch.

## Suggested next approach
- Consume `satisfiesTreeCondition_order_four_mixed_eq_of_childrenBag_eq` more directly in nearby order-4 theorem-level wrappers so the mixed family is uniformly canonicalized.
- After that, apply the same local pattern to the next remaining ordered wrapper in the nearest unfinished order-4 or order-5 family.

## Verification
- Ran:
  `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/RootedTree.lean`
- Ran:
  `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderConditions.lean`
