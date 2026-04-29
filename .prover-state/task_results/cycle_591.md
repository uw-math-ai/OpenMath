# Cycle 591 Results

## Worked on
Butcher §386 augmented convolution in
`OpenMath/ButcherGroup/Section386Aug.lean`, specifically the concrete
three-parallel-`node [leaf]` closed form and the matching unital
associativity sanity check.

## Approach
First inspected the two prior Aristotle result bundles requested by the
strategy.  Both were stub-based and not incorporated: `8c6ba006-...`
redefined `BTree` / `QuotEquiv` in a replacement `ButcherGroup.lean`, and
`c015ec03-...` imported fabricated mixed-slice modules and proved against
stubbed statements.

Added the two requested theorem statements with `sorry` and verified the
target file compiled in the sorry-first pass.  Then created five Aristotle
scaffolds under `.prover-state/aristotle_scaffolds/cycle_591/`:

- `bSeriesConvAug_three_singleton_leaves`
- `mul_assoc_at_three_singleton_leaves`
- `bSeriesConvAug_node_singleton_leaf_two_node_nils`
- `bSeriesConvAug_node_two_singleton_leaves_one_node_nil`
- `bSeriesConvAug_node_three_node_nils`

Submitted all five with separate `submit_directory` calls.  Aristotle
accepted only the headline closed-form scaffold as project
`afcfc981-e69b-4776-88d2-6bc18df1caab`; the other four calls returned
HTTP 429 "too many requests in progress", so they were not retried.
After the required 30-minute wait, the accepted project was still
`QUEUED`, so there was no Aristotle proof to incorporate this cycle.

Manual closure used the concrete cut enumeration directly:

- `bSeriesConvAug_three_singleton_leaves` closed with
  `simp [bSeriesConvAug, BTree.innerCut, BTree.innerCutForest]` and `ring`.
- `mul_assoc_at_three_singleton_leaves` closed by direct expansion with the
  unital hypotheses for `β.emptyVal` and `γ.emptyVal`, then `ring`.

## Result
SUCCESS.  Both requested theorems landed sorry-free:

- `bSeriesConvAug_three_singleton_leaves`
- `mul_assoc_at_three_singleton_leaves`

No new helper lemmas were needed in the live file; the concrete direct
expansion was small enough for Lean.

## Dead ends
No mathematical dead end this cycle.  The only external blocker was the
Aristotle 429 throttle on four of the five scaffold submissions.

## Discovery
The `n = 3` singleton-leaf case still admits a direct `simp`/`ring`
closure when the RHS keeps the asymmetric trunk positions explicit.  The
depth-3 unital associativity check can also be closed directly at this
size, without first landing private helpers for every mixed three-child
trunk.

The displayed closed form groups duplicate root-cut positions with
coefficients `3`, while keeping the asymmetric trunks
`[node [], node [leaf], node [leaf]]`,
`[node [leaf], node [], node [leaf]]`, and
`[node [leaf], node [leaf], node []]` separate.

## Suggested next approach
Use the `n = 1`, `n = 2`, and `n = 3` concrete closed forms as anchors for
the planned parametric disjoint-pair combinator over
`(S₁, S₂) : Finset (Fin n) × Finset (Fin n)` with `Disjoint S₁ S₂`.

The parametric proof should preserve list position order explicitly rather
than quotienting by symmetry.

## Verification
- `lake env lean OpenMath/ButcherGroup/Section386Aug.lean`
- `lake env lean OpenMath/ButcherGroup.lean`
- Aristotle project `afcfc981-e69b-4776-88d2-6bc18df1caab`: still
  `QUEUED` after the one post-wait refresh
