# Cycle 186 Results

## Worked on
- Aristotle triage for ready bundles `fc85413e-beac-4853-a531-42e884db6ce5` and `1911e575-52c8-493a-9338-e332b46a7dad`
- Bag-based canonicalization infrastructure for theorem-301A rooted-tree consumers
- Order-4 mixed two-child duplication in `OpenMath/OrderConditions.lean`

## Approach
- Inspected both ready Aristotle result directories before touching repo code.
- Read `OpenMath/RootedTree.lean` and `OpenMath/OrderConditions.lean` to identify where ordered child lists still leaked into theorem-301A proofs.
- Targeted the smallest real symmetric duplication cluster still in use: the order-4 mixed case `(1,2)` vs `(2,1)`.
- Added bag-facing infrastructure in `RootedTree.lean` for permuting ordered child witnesses:
  - `BTree.node_childrenBag_eq_of_perm`
  - `BTree.node_childrenBag_eq_swap`
- Replaced the separate `(1,2)` and `(2,1)` tree-condition lemmas in the order-4 mixed family with one canonical theorem:
  - `satisfiesTreeCondition_order_four_mixed_canonical`
- Used `satisfiesTreeCondition_eq_of_childrenBag_eq` plus `childrenBag` swap equality to route the `(2,1)` case through the canonical `(1,2)` branch.

## Result
- SUCCESS
- Bundle `fc85413e-beac-4853-a531-42e884db6ce5` was checked and skipped. It is Legendre-only, introduces replacement files outside the current theorem-301A target, and still contains stale bridge work rather than a tiny reusable helper for rooted trees.
- Bundle `1911e575-52c8-493a-9338-e332b46a7dad` was checked and skipped. It is likewise Legendre-era infrastructure with broad replacement files and remaining `sorry`s, incompatible with the current rooted-tree priority.
- `OpenMath/RootedTree.lean` now exposes bag-facing permutation lemmas for child witnesses.
- `OpenMath/OrderConditions.lean` no longer carries a separate order-4 `(2,1)` theorem branch; the reverse direction of `thm_301A_order4` now uses one bag-canonical mixed-case theorem.
- In that mixed order-4 cluster, theorem-301A consumers now use `childrenBag` through the swap canonicalization step instead of keeping two ordered-list branches.

## Dead ends
- Tried to canonicalize all order-1/order-2 children directly to `leaf` and `t2`, but the fallback representation still permits degenerate trees like `.node []` of order `1`, so equality-to-canonical-tree was too strong for this cycle.
- Adjusted to the correct representationally sound bag-first refactor: canonicalizing only the symmetric ordered leakage `[c₁, c₂]` vs `[c₂, c₁]`.

## Discovery
- Immediate-child `childrenBag` invariance is already strong enough to remove real ordered duplication in theorem-301A consumers, even before any deeper recursive quotient is introduced.
- The current fallback `List` encoding admits extra low-order representatives (`.node []`, etc.), so future “canonical tree” lemmas must be phrased carefully; bag-equality under permutation is safe, equality to textbook representatives is not generally safe yet.

## Suggested next approach
- Continue in the same style on the order-5 symmetric leakage:
  - three-child `(1,1,2)` permutations, or
  - two-child `(1,bushy3)` vs `(bushy3,1)` / `(1,chain3)` vs `(chain3,1)`
- Add small bag-permutation helpers for the relevant arities first, then replace one more duplicated theorem family with a canonical bag-based theorem.

## Verification
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/RootedTree.lean`
  - passed
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderConditions.lean`
  - passed
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build`
  - passed

## Aristotle job results
- Existing ready job `fc85413e-beac-4853-a531-42e884db6ce5`: inspected once, skipped as stale Legendre replacement output.
- Existing ready job `1911e575-52c8-493a-9338-e332b46a7dad`: inspected once, skipped as stale Legendre replacement output.
- No new Aristotle submissions were made this cycle because the active target had no open `sorry`s and the cycle’s scoped work was a local bag-based refactor rather than a new sorry-first proof decomposition.
