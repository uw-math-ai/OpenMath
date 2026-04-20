# Cycle 220 Results

## Worked on
- `OpenMath/RootedTree.lean` bag-first low-order witnesses
- `OpenMath/OrderConditions.lean` rewiring of the order-3/order-4 classifier stack and order-5 Case C / D witness builders

## Approach
- Read the cycle strategy and intentionally did not reopen the stale Legendre target or the already-landed order-5 dispatcher cleanup.
- Confirmed there were no ready Aristotle results at the start of the cycle and did not poll Aristotle.
- Added `BTree.OrderThreeWitness` with `order_three_witness_nonempty` / `order_three_witness`.
- Added `BTree.OrderFourWitness` with `order_four_witness_nonempty` / `order_four_witness`.
- Downgraded `order_three_cases` and `order_four_cases` to compatibility wrappers in `RootedTree.lean` built from the new witness APIs.
- Rewired `thm_301A_order3`, `thm_301A_order4`, `order_five_caseC_witness_nonempty`, and `order_five_caseD_witness_nonempty` to consume the new bag-first witness API.
- Verified with:
  - `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/RootedTree.lean`
  - `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderConditions.lean`
  - `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build`

## Result
- SUCCESS
- `OrderThreeWitness` and `OrderFourWitness` were added in `RootedTree.lean`.
- `order_five_caseC_witness_nonempty` now uses `BTree.order_three_witness`.
- `order_five_caseD_witness_nonempty` now uses `BTree.order_four_witness`, and recurses through `BTree.order_three_witness` in the singleton-child branch.
- `OrderConditions.lean` no longer defines or directly depends on local `order_three_cases` / `order_four_cases`.
- The old `order_three_cases` / `order_four_cases` remain only as thin compatibility wrappers in `RootedTree.lean`.

## Dead ends
- The first compile failed because the new witness proofs were placed above `order_pos`; I replaced those calls with local positivity facts instead of moving the theorem.
- Dependent pattern matching on the new indexed witnesses required using refined `_` / `.node [...]` terms rather than outer variable names that disappear after `cases`.

## Discovery
- Moving the classifier logic into `RootedTree.lean` is enough to remove the direct ordered-list theorem dependency from the theorem-level classifier stack without rewriting the downstream elementary-weight lemmas yet.
- Keeping the legacy case theorems as wrappers gives a clean compatibility boundary while the unordered representation upgrade is still in progress.

## Suggested next approach
- Continue replacing existential ordered-list witness plumbing in `OrderConditions.lean` helper lemmas with direct `OrderThreeWitness` / `OrderFourWitness` consumers so the remaining low-order infrastructure is uniformly bag-first.
- If the next cycle touches order-4 singleton-child infrastructure again, consider introducing dedicated helper adapters from `OrderFourWitness.single3` into the order-5 canonical singleton-child lemmas to reduce repeated existential packaging.
