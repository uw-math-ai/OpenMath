# Cycle 241 Results

## Worked on
- Replaced the order-3 / order-4 exact-list recovery boundary in `OpenMath/RootedTree.lean` with bag-first recovery witnesses.
- Updated theorem-side order-3 / order-4 consumers in `OpenMath/OrderConditions.lean` to case-split on the new recovery witnesses.

## Approach
- Audited the remaining live recovery API: `OrderThreeBagWitness`, `OrderFourBagWitness`, `order_three_bag_witness_recover`, `order_four_bag_witness_recover`, and the existing order-5 normalized witness families.
- Introduced `BTree.OrderThreeRecoveryWitness` and `BTree.OrderFourRecoveryWitness` so the recovery layer keeps only child-bag equalities and low-order facts.
- Changed `order_three_bag_witness_recover` and `order_four_bag_witness_recover` from proposition-valued exact-node recovery theorems into data-returning bag-first recovery defs.
- Reworked `order_five_caseD_witness_nonempty` to consume the new order-4 recovery witness directly.
- Reworked `thm_301A_order3` and `thm_301A_order4` to use the new recovery witnesses instead of relying on ordered-node equalities.

## Result
- SUCCESS: the remaining order-3 / order-4 recovery API is now bag-first, and theorem-side order-3 / order-4 consumers were updated in the same cycle.
- Verification succeeded with:
  - `lake env lean OpenMath/RootedTree.lean`
  - `lake env lean OpenMath/OrderConditions.lean`
  - `lake build OpenMath.RootedTree OpenMath.OrderConditions`

## Dead ends
- `order_three_bag_witness_recover` and `order_four_bag_witness_recover` could not remain `theorem`s after the refactor, because their new return types are witness data rather than propositions. They had to become `def`s.
- Rewriting directly from `t.childrenBag = ...` inside theorem-side consumers failed until the proofs first case-split on `t = .node children`; the bag-equality transport lemmas are stated for explicit node lists.
- The singleton-child order-4 branches also needed a local `cases child3` split before applying `satisfiesTreeCondition_singleton_eq_of_childrenBag_eq`, because that lemma is list-indexed on the child node.

## Discovery
- The old exact-list recovery theorems were already only live inside `RootedTree.lean`; `OrderConditions.lean` was mostly consuming normalized witness families already. The visible theorem-side migration needed this cycle was at order 3 / order 4, not the order-5 Case C / Case D dispatchers themselves.
- `OrderFiveCaseDWitness` already had the right bag-first payload shape, so the main remaining work was exposing an order-4 recovery witness with the same style and feeding it into the existing Case D constructor.

## Suggested next approach
- Remove any remaining stale references or comments that describe the order-3 / order-4 recovery API as exact-list based.
- If the planner still sees representation-boundary debt, audit whether any other theorem-side helpers are still destructuring `OrderThreeBagWitness` / `OrderFourBagWitness` directly instead of going through the new recovery witness layer.
- Aristotle status for this cycle: no incorporation was available at the start, and no fresh batch was submitted because the cycle strategy explicitly said not to start with a new Aristotle batch.
