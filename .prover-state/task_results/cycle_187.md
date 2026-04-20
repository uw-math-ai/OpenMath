# Cycle 187 Results

## Worked on
Order-5 three-child symmetric duplication in `OpenMath/OrderConditions.lean`, specifically the `(1,1,2)` family with ordered witnesses `[1,1,2]`, `[1,2,1]`, and `[2,1,1]`.

## Approach
Added small bag-facing canonicalization lemmas in `OpenMath/RootedTree.lean` for three-child nodes:

- `BTree.node_childrenBag_eq_swap_right`
- `BTree.node_childrenBag_eq_rotate_left`

Then refactored the downstream order-condition consumer proofs so the permuted `(1,2,1)` and `(2,1,1)` cases route through the canonical `(1,1,2)` theorem using `satisfiesTreeCondition_eq_of_childrenBag_eq`, instead of duplicating the density/elementary-weight argument.

Aristotle was intentionally skipped this cycle. The planner strategy and local `.prover-state/strategy.md` both said there were no active `sorry`s and no pending Aristotle bundles, and this refactor did not introduce new `sorry`s.

## Result
SUCCESS.

New infrastructure landed in `OpenMath/RootedTree.lean`, and one real theorem-301A consumer duplication cluster was reduced in `OpenMath/OrderConditions.lean`:

- `satisfiesTreeCondition_order_five_3child_121` now canonicalizes to `[1,1,2]` via `node_childrenBag_eq_swap_right`
- `satisfiesTreeCondition_order_five_3child_211` now canonicalizes to `[1,1,2]` via `node_childrenBag_eq_rotate_left`

The canonical theorem `satisfiesTreeCondition_order_five_3child_112` remains the single proof carrying the actual order-5 `(1,1,2)` calculation.

## Dead ends
The first direct `lake env lean OpenMath/OrderConditions.lean` run failed because the new `RootedTree` theorem names were not yet available through the imported build artifacts. Rebuilding `OpenMath.RootedTree` fixed that; no proof changes were needed.

## Discovery
The `(1,1,2)` cluster is a clean bag-first target because the downstream theorem family already shared the same right-hand-side analytic expression and only differed by ordered child witnesses. This made bag-equality transport strictly cheaper than maintaining three parallel proof scripts.

## Suggested next approach
Continue the same pattern on the next order-5 symmetric duplication cluster:

- either `[1,bushy3]` versus `[bushy3,1]`, or
- `[1,chain3]` versus `[chain3,1]`.

The existing `satisfiesTreeCondition_eq_of_childrenBag_eq` transport plus the two-child swap bag lemma should make one of those pairs collapse in the same style.

## Verification
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/RootedTree.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build OpenMath.RootedTree`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderConditions.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build`

All commands passed. `OrderConditions.lean` and unrelated project files still emit pre-existing linter warnings/info suggestions, but there were no build errors.
