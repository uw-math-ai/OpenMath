# Cycle 131 Results

## Worked on
Theorem 342l in `OpenMath/Collocation.lean`:
- decomposed `B(2n) ∧ C(n) ∧ D(n) ⇒ G(2n)` into focused local sublemmas
- proved the top-level theorem `hasTreeOrder_of_B_C_D` from that decomposition by strong induction
- updated `plan.md` to reflect that 342j/342k and the order-5 tree infrastructure are complete

## Approach
1. Read `.prover-state/strategy.md` and checked the existing 342l proof site in `OpenMath/Collocation.lean`.
2. Reviewed the ready Aristotle result bundle `30d4f0dd...`; it only recreated infrastructure already present in-tree, so nothing was harvested.
3. Added local helpers:
   - `childrenOf`
   - `childDensityProd`
   - `elementaryWeight_simplified_of_C`
   - `ew_simplified_of_C`
   - `tree_cond_all_small`
   - `tree_cond_one_big`
4. Replaced the monolithic `hasTreeOrder_of_B_C_D` sorry with a strong-induction proof that splits on whether a child has order `> n`.
5. Verified the file compiles in its decomposed state with:
   `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/Collocation.lean`
6. Submitted four Aristotle jobs on the new subgoals:
   - `15213cb3-7914-436e-a1e2-850643839ce5` — `elementaryWeight_simplified_of_C`
   - `0d159403-801c-43d9-b4e1-6465cf9beb3a` — `ew_simplified_of_C`
   - `c24f253f-ff04-4a7d-90a8-3c9be1452b17` — `tree_cond_all_small`
   - `df09be51-ee25-44f3-8265-888ec1b523ad` — top-level 342l attempt
7. Started the mandated `sleep 1800` wait window and performed one status check afterward.

## Result
PARTIAL SUCCESS — 342l is now decomposed into four local proof obligations, and the exported theorem
`hasTreeOrder_of_B_C_D` no longer contains a `sorry`.

Current open declarations in `OpenMath/Collocation.lean`:
- `elementaryWeight_simplified_of_C`
- `ew_simplified_of_C`
- `tree_cond_all_small`
- `tree_cond_one_big`

Aristotle status at the cycle’s single check:
- `15213cb3...` — `IN_PROGRESS` (5%)
- `0d159403...` — `IN_PROGRESS` (2%)
- `c24f253f...` — `IN_PROGRESS` (3%)
- `df09be51...` — `IN_PROGRESS` (12%)

## Dead ends
- Attempting to push directly through the one-big-child case still runs into the same-order grafted-tree term after applying `D(n)`.
- A plain strong induction on tree order is not enough for `tree_cond_one_big`; the correction term has the same total order as the original tree.

## Discovery
- The right shape is to isolate the hard part in `tree_cond_one_big` and keep the outer theorem fully structured.
- The top-level induction can be completed cleanly with motive
  `∀ u, u.order = m → u.order ≤ 2*n → satisfiesTreeCondition u`.
- The blocker is genuinely local to the one-big-child reduction, not the global recursion setup.

## Suggested next approach
1. Harvest the four Aristotle jobs once they complete; `elementaryWeight_simplified_of_C` and `tree_cond_all_small` are the most likely to come back usable.
2. For `tree_cond_one_big`, add a second induction parameter or auxiliary grafted-tree functional, following Hairer–Nørsett–Wanner IV.5 more literally.
3. Keep the current decomposition; do not revert to a monolithic 342l proof.
