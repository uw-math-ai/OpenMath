# Cycle 201 Results

## Worked on
Migrated the order-5 `{1, chain3}` family in `OpenMath/OrderConditions.lean` from orientation-specific two-child proofs to a canonical-plus-bag-transport shape.

Did not start `{1, bushy3}` this cycle.

## Approach
Kept the canonical orientation `[order-1, chain-3]` as the base proof and moved the normalization boundary down to `childrenBag`.

Added three bag-facing helpers for the `{1, chain3}` family:
- `ew_of_order_five_chain3_eq_of_childrenBag_eq`
- `density_of_order_five_chain3_eq_of_childrenBag_eq`
- `satisfiesTreeCondition_order_five_chain3_eq_of_childrenBag_eq`

Rewired the reverse-orientation theorem `satisfiesTreeCondition_order_five_chain3_1` and the family wrapper `satisfiesTreeCondition_order_five_chain3_canonical` to use the bag-facing transport helper with `BTree.node_childrenBag_eq_swap`.

Deleted the duplicated reverse ordered proof scripts:
- `ew_of_order_five_chain3_1`
- `density_of_order_five_chain3_1`

## Result
SUCCESS

The `{1, chain3}` family now has:
- one canonical ordered proof for `ew`
- one canonical ordered proof for density
- one bag-facing transport layer
- no duplicated reverse-orientation ordered `ew` or density proof script

The reverse `satisfiesTreeCondition` route is now a thin wrapper over bag transport instead of a separate ordered proof path.

## Dead ends
Initial helper signatures used dotted `.node` notation in a context where Lean could not infer the inductive type. Replaced those occurrences with explicit `BTree.node`.

The first transport proof attempt rewrote in the wrong direction. Replaced it with direct `.trans` composition from `elementaryWeight_eq_of_childrenBag_eq` and `BTree.density_eq_of_childrenBag_eq`.

## Discovery
For this family, the cleanest normalization point is not the final canonical wrapper but the intermediate `{1, chain3}` transport theorem. Once that theorem is bag-facing, both the reverse orientation and the family wrapper collapse naturally.

The same pattern should apply directly to `{1, bushy3}` next cycle.

## Suggested next approach
Apply the same refactor to `{1, bushy3}`:
- add bag-facing `ew`/density/`satisfiesTreeCondition` transport helpers
- delete the reverse ordered `ew` and density lemmas
- make the reverse tree-condition theorem and canonical wrapper consume the bag-facing helper

## Aristotle
Skipped Aristotle this cycle.

Reason: the repository started with no live `sorry`s, and this refactor was completed without introducing new `sorry`s, so there was no batch of focused pending subgoals to submit.

## Verification
Ran:

```bash
export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH
lake env lean OpenMath/RootedTree.lean

export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH
lake env lean OpenMath/OrderConditions.lean
```

`OpenMath/OrderConditions.lean` emitted existing linter warnings about unused `simp` arguments and `ring` suggestions outside the touched area, but compiled successfully.
