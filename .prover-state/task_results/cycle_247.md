# Cycle 247 Results

## Worked on
Theorem 301A order-4 representation boundary in `OpenMath/OrderConditions.lean`:
- `satisfiesTreeCondition_order_four_via_bushy3`
- `satisfiesTreeCondition_order_four_via_chain3`
- the reverse branch of `thm_301A_order4`

## Approach
Audited the live order-4 rooted-tree API first:
- `BTree.OrderFourBagWitness`
- `BTree.order_four_bag_witness_recover`
- `satisfiesTreeCondition_eq_of_childrenBag_eq`
- `satisfiesTreeCondition_singleton_eq_of_tree_childrenBag_eq`

Then:
- renamed the old exact-list order-4 theorems to private `_exact` helpers;
- added bag-first wrappers for the via-bushy3 and via-chain3 order-4 families using child-bag equalities instead of theorem-local exact-list existential hypotheses;
- rewired both forward order-4 canonical uses and the reverse branch of `thm_301A_order4` to call the new bag-first wrappers directly from recovery output.

Per the cycle strategy, I did not submit a fresh Aristotle batch because there were no completed results ready and the planner explicitly said not to start a new batch this cycle.

## Result
SUCCESS

Visible Lean-code progress:
- both order-4 family theorems now expose bag-first boundaries;
- the `singleBushy3` and `singleChain3` reverse cases in `thm_301A_order4` no longer reconstruct exact singleton/list witnesses just to call the theorem.

## Dead ends
Initial rewrite attempts failed because `rw` did not unfold `t4c` / `t4d` automatically and because the post-rewrite reverse goals were on `.node [child3]`, not `.node children`. Fixed by:
- inserting `change` on the forward canonical cases;
- applying the wrappers on `[child3]` after the outer bag-equivalence rewrite in the reverse cases.

## Discovery
No `RootedTree.lean` changes were needed. The existing private singleton bag-equivalence theorem in `OrderConditions.lean` was enough to bridge the public order-4 recovery witness to the old exact computational lemmas.

## Suggested next approach
The order-4 representation boundary targeted by the planner is now bag-first on both via-bushy3 and via-chain3 branches. The next pass should look for the next immediate theorem-local exact-list consumer in the same Theorem 301A neighborhood before broadening scope.
