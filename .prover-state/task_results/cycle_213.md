# Cycle 213 Results

## Worked on
Unary mixed `{1,2}` order-5 infrastructure in `OpenMath/OrderConditions.lean`, specifically the remaining reverse-orientation wrapper boundary around the singleton-child mixed family.

## Approach
Re-read the live mixed-family lemmas and theorem-level callers targeted by the planner:
- `ew_of_order_five_via_mixed_eq_of_childrenBag_eq`
- `satisfiesTreeCondition_order_five_via_mixed_eq_of_childrenBag_eq`
- `satisfiesTreeCondition_order_five_via_mixed_canonical`
- the Case D dispatchers and `thm_301A_order5`

Confirmed there were no ready Aristotle results to incorporate this cycle, per strategy. Also confirmed the theorem-level callers were already routed through `satisfiesTreeCondition_order_five_via_mixed_canonical`, so the remaining work was to eliminate the stale reverse `[2,1]` wrappers as named proof boundaries.

Removed:
- `ew_of_order_five_via_mixed21`
- `satisfiesTreeCondition_order_five_via_mixed21`

Then tightened `satisfiesTreeCondition_order_five_via_mixed_canonical` so the forward `[1,2]` branch uses the canonical computational theorem directly, while the reverse `[2,1]` branch is handled only by `childrenBag` transport via `BTree.node_childrenBag_eq_swap`.

## Result
SUCCESS.

The unary mixed `{1,2}` family is now canonicalized at theorem level:
- canonical computational theorem: `satisfiesTreeCondition_order_five_via_mixed12`
- family transport lemma: `satisfiesTreeCondition_order_five_via_mixed_eq_of_childrenBag_eq`
- canonical unordered-family boundary: `satisfiesTreeCondition_order_five_via_mixed_canonical`

The reverse-orientation wrappers were removed entirely, so `[2,1]` is no longer an independent theorem-level boundary.

`RootedTree.lean` did not need any helper; existing `BTree.node_childrenBag_eq_swap` was sufficient.

## Dead ends
No blocker in the caller path. After re-reading the Case D dispatcher and `thm_301A_order5`, there was no remaining theorem-level use of `_via_mixed21`; only the obsolete wrapper definitions themselves remained.

## Discovery
The theorem-level canonicalization for this family had effectively already landed in prior cycles. The remaining cleanup was definitional: removing dead reverse wrappers and making the canonical theorem explicitly use the direct `[1,2]` branch plus swap transport for `[2,1]`.

Because this cycle was a wrapper-removal refactor with no new `sorry`s or standalone proof subgoals, there was no same-cycle Aristotle batch to submit without manufacturing artificial obligations. In line with the strategy, I also did not poll any stale Aristotle jobs.

## Suggested next approach
Continue checking the order-5 rooted-tree infrastructure for any remaining dead ordered-wrapper boundaries near the canonical dispatchers, but avoid broad refactors unless a live caller still depends on an ordered orientation lemma.

## Verification
Ran:

```bash
export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH
lake env lean OpenMath/OrderConditions.lean
```

Result: success, with pre-existing warnings only.
