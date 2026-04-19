# Cycle 126 Results

## Worked on
- Extended rooted tree infrastructure (`OpenMath/RootedTree.lean`): order-5 census + structural lemmas
- Created elementary weight framework (`OpenMath/OrderConditions.lean`): Theorem 301A via rooted trees

## Approach
1. Added all 9 trees of order 5 (t5a–t5i) with `native_decide` verification of order, symmetry, density, beta, alpha.
2. Proved structural theorems: `order_pos`, `order_node_sum`, `density_pos`, `symmetry_pos` — all without sorry. Used well-founded recursion via `termination_by sizeOf` to handle the nested inductive BTree type.
3. Created `OpenMath/OrderConditions.lean`:
   - Defined `elementaryWeight` (recursive on BTree, using `List.foldr`)
   - Defined `satisfiesTreeCondition` and `hasTreeOrder`
   - Proved connection lemmas: `satisfiesTreeCondition_leaf`, `satisfiesTreeCondition_t2`, `satisfiesTreeCondition_t2_of_consistent`
   - Proved `thm_301A_order1` (no sorry)
   - Proved `thm_301A_order2` (no sorry) with helper lemmas for tree enumeration (`ew_of_order_one/two`, `density_of_order_one/two`)
   - Stated `thm_301A_order3/4/5` with sorry
4. Submitted OrderConditions.lean to Aristotle (project `4cce0cc4`) for the remaining 3 sorry's.

## Result
SUCCESS — all targets completed:
- 9 order-5 trees defined and verified
- 4 structural lemmas proved (order_pos, order_node_sum, density_pos, symmetry_pos)
- Elementary weight framework established with `elementaryWeight`, `satisfiesTreeCondition`, `hasTreeOrder`
- Theorem 301A proved at orders 1 and 2 (fully, no sorry)
- Theorem 301A stated at orders 3, 4, 5 (with sorry — pending tree enumeration)
- All modified files compile cleanly
- 3 sorry's in new file (OrderConditions.lean), 0 in existing files

## Dead ends
- `induction t` doesn't work on nested inductive `BTree` — had to use equation-compiler style with `termination_by sizeOf` for `density_pos` and `symmetry_pos`
- `List.mem_cons_self` in current Lean 4 has implicit args; must use `.head ..` constructor instead
- `interval_cases t.order` didn't work cleanly for the reverse direction of 301A; used `by_cases` instead
- `lake env lean` and `lake build` had git/mathlib issues; used Lean LSP (`lean_build`) for verification instead

## Discovery
- The well-founded recursion pattern for BTree works well: define theorem by equation compiler, use `termination_by sizeOf`, same `decreasing_by` proof as existing `order`/`density` definitions
- The elementary weight has the right structure: `elementaryWeight tab (.node [.leaf, .leaf]) i = (∑ k, A i k)^2`, matching order3a's c_i^2 under consistency
- Theorem 301A reverse direction (HasOrderGeN → hasTreeOrder N) requires enumerating all BTree values of each order and showing their elementary weights match — this is the hard direction. Helper lemmas `ew_of_order_one/two` and `density_of_order_one/two` abstract the key pattern
- Aristotle project `8a9315e1` returned API 500 error at start of cycle

## Suggested next approach
1. Close `thm_301A_order3`: enumerate order-3 trees (2 shapes: .node [c1,c2] with c1.order=c2.order=1, and .node [c] with c.order=2). Add `ew_of_order_three` helper.
2. Close `thm_301A_order4/5`: same pattern, more cases (4 and 9 shapes respectively).
3. Check Aristotle project `4cce0cc4` for results.
4. Start connecting order conditions to Theorem 342C (trees → RK order → stability implications).
