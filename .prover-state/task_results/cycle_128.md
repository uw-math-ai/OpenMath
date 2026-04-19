# Cycle 128 Results

## Worked on
`OpenMath/OrderConditions.lean`, specifically `thm_301A_order4`.

## Approach
Added the full order-4 helper layer following the order-3 pattern:
- `order_four_cases`
- elementary-weight lemmas for bushy, mixed, and single-child order-4 trees
- density lemmas for the same shapes
- sum-conversion lemmas `order4a_sum_eq` through `order4d_sum_eq`
- tree-condition equivalences for each order-4 shape

Then proved both directions of `thm_301A_order4` by evaluating the explicit order-4 trees in the forward direction and using `order_four_cases` plus `order_three_cases` in the reverse direction.

## Result
SUCCESS — `thm_301A_order4` was proved, reducing the file’s sorry count from 2 to 1 and leaving only `thm_301A_order5`.

## Dead ends
- The worker hit the API output limit before completing the cycle bookkeeping, so the code landed without `cycle_128.md` or the cycle counter update.

## Discovery
- The order-4 proof pattern is fully reusable for order 5: classify tree shapes by the partition of child orders, derive elementary-weight and density formulas per shape, then connect each shape to the matching Runge–Kutta order condition.

## Suggested next approach
Target `thm_301A_order5` with the same decomposition pattern, using the 9 order-5 rooted tree shapes and the existing `t5a`–`t5i` definitions in `RootedTree.lean`.
