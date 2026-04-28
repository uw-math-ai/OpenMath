# Cycle 519 Results

## Worked on
§384 convolution prep in `OpenMath/ButcherGroup.lean`:
- Headline: `ButcherProduct.elementaryWeight_castAdd`, the upper-left
  block elementary-weight reduction for `ButcherProduct`.
- Stretch: raw representative-level `ButcherTableau.bSeries`,
  `ButcherProduct.bSeries_castAdd`, and
  `ButcherProduct.elementaryWeight_natAdd_node_eq_powerset_sum_bSeries`,
  which rewrites the cycle 518 powerset identity so the cut factor is
  `t₁.bSeries`.

## Approach
Used the cycle-497/cycle-510 nested `BTree.rec` pattern rather than
ordinary induction:
- `motive_1` proves the tree-level cast-add reduction.
- `motive_2` tracks the node `List.foldr` body over the child list.
- In the cons case, split the inner `Fin (s+t)` sum with
  `Fin.sum_univ_add`, killed the upper-right block with
  `simp [ButcherProduct]`, rewrote the upper-left block with the child
  IH, and simplified the block matrix entry.

For the stretch theorem, first proved the weighted cut-side corollary
`ButcherProduct.bSeries_castAdd`. Then applied the existing raw powerset
identity from cycle 518, rewrote each cut factor, collapsed
`univ.powerset` to the full finite sum, and reindexed by finite-set
complement so the index set records kept children.

## Result
SUCCESS — `OpenMath/ButcherGroup.lean` is sorry-free and compiles with
both deliverables.

Verified with:
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build`

`plan.md` was updated in the §381/§384 notes to record the cycle 519
upper-left block reduction and bSeries-form powerset identity.

## Aristotle batch
Created five scaffolds in
`.prover-state/aristotle_scaffolds/cycle_519/`:
- `elementaryWeight_castAdd_leaf.lean`
- `upperRight_block_zero.lean`
- `elementaryWeight_castAdd_node.lean`
- `elementaryWeight_castAdd_full.lean`
- `bSeries_castAdd_corollary.lean`

Submitted all five at cycle start. Every submission returned HTTP 429
("too many requests in progress") immediately and produced no project ID,
so there were no Aristotle jobs to sleep on or refresh. No retries were
attempted; manual closure carried the cycle.

## Dead ends
- In the first manual proof attempt, `simp [ButcherProduct, ih_head k]`
  unfolded the tableau record inside `elementaryWeight` before the child
  IH could match, leaving a `mul_eq_mul_left_iff`-style disjunction.
  Rewriting by `ih_head k` first and only then simplifying
  `ButcherProduct` fixed the issue.

## Discovery
- The upper-left block proof is essentially the `padRight` proof shape,
  but the ordering of rewrites matters: do not unfold `ButcherProduct`
  around an `elementaryWeight` occurrence before applying the child IH.
- For the bSeries-form node identity, the cycle 518 powerset orientation
  indexes cut children. Reindexing by `S ↦ Sᶜ` turns it into the more useful
  "kept children" orientation:
  cut factors over `Sᶜ`, kept factors over `S`.

## Suggested next approach
Next, recurse on the "kept" side of
`ButcherProduct.elementaryWeight_natAdd_node_eq_powerset_sum_bSeries` to
replace the remaining lower-right
`(ButcherProduct t₁ t₂).elementaryWeight (children.get p) (Fin.natAdd s j₂)`
factors with the closed-form `(trunk, cuts)` decomposition. This is the
next §384 layer needed before returning to `IsG1Equiv.product_congr` and
`G1.mul`.
