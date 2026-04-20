# Cycle 200 Results

## Worked on
Order-5 rooted-tree infrastructure in `OpenMath/OrderConditions.lean`, specifically the `{1,1,2}` three-child permutation cluster used in Case B of `thm_301A_order5`.

## Approach
Kept the existing canonical `{1,1,2}` theorem for the ordered representative and replaced the two extra orientation-specific lemmas with a single bag-facing transport wrapper:
`satisfiesTreeCondition_order_five_3child_eq_of_childrenBag_eq`.

Then rewired `satisfiesTreeCondition_order_five_3child_canonical` to route the non-canonical permutations through `childrenBag` equalities (`swap_right` and `rotate_left`) instead of separate ordered-child proof scripts.

I did not touch the inductive tree representation and did not refactor unrelated order-5 families.

## Result
SUCCESS — one full remaining order-5 permutation family now dispatches through the `childrenBag` interface.

New bag-facing helper introduced:
- `satisfiesTreeCondition_order_five_3child_eq_of_childrenBag_eq`

Ordered-child duplication removed:
- deleted the dedicated `[1,2,1]` wrapper
- deleted the dedicated `[2,1,1]` wrapper
- kept one canonical `{1,1,2}` theorem and transported the other orientations through bag equality

`thm_301A_order5` still uses the same family-level canonical wrapper, but that wrapper is now bag-driven for the non-canonical orientations.

## Dead ends
No substantive blocker this cycle.

I considered forcing a fresh Aristotle round, but the planner state for cycle 200 explicitly said to submit fresh Aristotle jobs only if I introduced new focused `sorry`s. This refactor was completed directly without introducing new `sorry`s, so Aristotle was skipped.

## Discovery
The remaining ordered duplication in the order-5 proof boundary is concentrated in family-level wrappers, not the main theorem itself. The `{1,1,2}` cluster was already close to a bag-facing interface; the missing piece was a reusable transport theorem from a canonical ordered witness to any bag-equal orientation.

The same pattern should apply to other residual orientation-sensitive families, especially where a canonical theorem already exists and only the non-canonical branches still use bespoke wrappers.

## Suggested next approach
Apply the same bag-facing reduction to one of the two-child order-5 families that still has paired orientation-specific wrappers, most likely:
- `{1, bushy-3}`
- `{1, chain-3}`

Those should be reducible to one canonical theorem plus a bag-transport wrapper, analogous to the `{1,1,2}` refactor completed here.

## Verification
Commands run:

```bash
export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH
lake env lean OpenMath/OrderConditions.lean
lake env lean OpenMath/RootedTree.lean
```

Both commands completed successfully. `OrderConditions.lean` emitted pre-existing linter warnings unrelated to this refactor.
