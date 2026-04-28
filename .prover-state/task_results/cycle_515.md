# Cycle 515 Results

## Worked on
Butcher §383 `G1(p)` quotient construction in
`OpenMath/ButcherGroup.lean`.

## Approach
Followed the sorry-first scaffold from the strategy, placing the new layer
after the cycle-514 `IsG1Equiv` bridge lemmas:
- `g1Setoid p` on `Σ s, QuotEquiv s`
- quotient carrier `G1 p`
- projection `G1.mk`
- order-restricted coefficient lift `G1.bSeriesHomAt`
- guarded tree-condition lift `G1.satisfiesTreeCondition`
- quotient-level order predicate `G1.hasTreeOrder`
- `_mk` computation lemmas for all three lifted invariants

The value lift used Option A. `G1.bSeriesHomAt p τ hτ` fixes a tree with
`τ.order ≤ p`, so quotient well-definedness is exactly the defining
`IsG1Equiv p` equality applied to `τ` and `hτ`.

For `G1.satisfiesTreeCondition`, the total tree-indexed predicate is guarded:
`τ.order ≤ p → q.satisfiesTreeCondition τ`. This makes the predicate
representative-independent outside the range controlled by `IsG1Equiv p`,
while reducing to the ordinary representative condition for trees of order
at most `p`.

## Result
SUCCESS. The new declarations are sorry-free, and
`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean`
succeeds.

`plan.md` was updated in both the §383 status entry and the Current Target
body to record the landed quotient layer. The current target was not rotated.

## Aristotle
Submitted the planned five-file batch:
1. `g1Setoid` `iseqv`
2. `G1.bSeriesHomAt_mk`
3. `G1.satisfiesTreeCondition_mk`
4. `G1.hasTreeOrder_mk`
5. `G1.hasTreeOrder` well-definedness

All five submissions immediately returned HTTP 429:
`You have too many requests in progress. Please cancel or wait for a project to complete before starting a new one.`
Per the strategy, no retries were attempted. The obligations were closed
manually.

## Dead ends
No Lean-level dead ends. The only external blocker was Aristotle capacity.

## Discovery
- The `Setoid` proof is direct from `IsG1Equiv.refl`, `.symm`, and `.trans`.
- The restricted coefficient lift is the clean quotient API: no total
  `BTree → ℝ` lift is available from `IsG1Equiv p`, but a fixed tree with
  `τ.order ≤ p` is well-defined.
- A total `G1.satisfiesTreeCondition : G1 p → BTree → Prop` must guard the
  representative predicate by `τ.order ≤ p`; otherwise the quotient relation
  does not determine values on higher-order trees.

## Suggested next approach
Cycle 516 should start the `G1 p` multiplication layer:
- prove an `IsG1Equiv.product_congr` lemma for `QuotEquiv.product`
- lift `QuotEquiv.product` to `G1.mul`
- add the zero-stage identity as the `G1` identity candidate

Do not reopen the §384 convolution theorem until
`.prover-state/issues/butcher_section384_convolution.md` is addressed.
