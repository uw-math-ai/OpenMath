# Cycle 202 Results

## Worked on
Theorem 301A rooted-tree infrastructure in `OpenMath/OrderConditions.lean`, specifically the order-5 two-child `{1, bushy3}` family:
- `ew_of_order_five_1_bushy3`
- `ew_of_order_five_bushy3_1`
- `density_of_order_five_1_bushy3`
- `density_of_order_five_bushy3_1`
- `satisfiesTreeCondition_order_five_1_bushy3`
- `satisfiesTreeCondition_order_five_bushy3_1`
- `satisfiesTreeCondition_order_five_bushy3_canonical`

## Approach
Matched the cycle 201 `{1, chain3}` normalization pattern exactly.

Kept the canonical ordered proofs for `[1, bushy3]` and introduced a bag-facing transport layer at the family boundary:
- `ew_of_order_five_bushy3_eq_of_childrenBag_eq`
- `density_of_order_five_bushy3_eq_of_childrenBag_eq`
- `satisfiesTreeCondition_order_five_bushy3_eq_of_childrenBag_eq`

Then rewired the reverse orientation and canonical family wrapper to normalize through `BTree.node_childrenBag_eq_swap` and the new bag-facing helpers instead of maintaining separate ordered reverse proofs.

Aristotle was skipped this cycle. The planner explicitly marked cycle 202 as non-Aristotle unless a new focused `sorry` was introduced during the migration; this refactor was completed without introducing any `sorry`.

## Result
SUCCESS — the `{1, bushy3}` family now has the same canonical-plus-bag-transport shape as `{1, chain3}`.

Reverse-orientation ordered proof scripts collapsed:
- `ew_of_order_five_bushy3_1` no longer contains its own ordered simplification proof; it now transports through `ew_of_order_five_bushy3_eq_of_childrenBag_eq`.
- `density_of_order_five_bushy3_1` no longer contains its own ordered density proof; it now transports through `density_of_order_five_bushy3_eq_of_childrenBag_eq`.
- `satisfiesTreeCondition_order_five_bushy3_1` now consumes `satisfiesTreeCondition_order_five_bushy3_eq_of_childrenBag_eq`.
- `satisfiesTreeCondition_order_five_bushy3_canonical` now uses the bag-facing helper directly in the reverse branch rather than routing through a bespoke reverse proof path.

## Dead ends
The first edit placed the new bushy3 transport helpers after the reverse theorems that use them. Lean rejected that with unknown-identifier errors, so I moved the new helper declarations earlier to match the working `{1, chain3}` layout.

## Discovery
For the two-child order-5 families, the clean normalization boundary is the family-level bag transport theorem, not the outer wrapper theorem. Once `ew` and density are transported at that level, both the reverse orientation theorem and the canonical wrapper reduce to short `simpa` proofs.

The next remaining orientation-duplicated order-5 family under a unary parent appears to be the mixed `[1,2]` / `[2,1]` branch (`via_mixed12` / `via_mixed21`), but I did not start that refactor this cycle.

## Suggested next approach
Apply the same canonical-plus-bag-transport refactor to the unary mixed order-5 family:
- normalize the inner two-child `[1,2]` vs `[2,1]` witness through `childrenBag`,
- add family-level `ew` / density / `satisfiesTreeCondition` transport helpers,
- then collapse the reverse-orientation theorem to a transport proof.

## Verification
Ran:

```bash
export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH
lake env lean OpenMath/RootedTree.lean
lake env lean OpenMath/OrderConditions.lean
```
