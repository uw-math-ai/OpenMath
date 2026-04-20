# Cycle 237 Results

## Worked on
Moved the order-5 Case B three-child normalization witness from
`OpenMath/OrderConditions.lean` into the public rooted-tree API in
`OpenMath/RootedTree.lean`, then refactored the reverse Case B branch of
`thm_301A_order5` to consume the new `BTree` witness directly.

## Approach
Audited the existing order-5 infrastructure first:
- confirmed `BTree.OrderFiveCaseCWitness` was already public and consumed;
- confirmed the order-5 singleton-child Case D bag-witness recovery was already
  public and consumed;
- confirmed the `{1,1,2}` Case B classifier still lived privately in
  `OrderConditions.lean`.

Then:
- added public `BTree.OrderFiveCaseBWitness`,
  `BTree.order_five_caseB_witness_nonempty`, and
  `BTree.order_five_caseB_witness` in `OpenMath/RootedTree.lean`;
- removed the theorem-local Case B witness stack from
  `OpenMath/OrderConditions.lean`;
- updated the Case B dispatcher and both theorem sites to use the new public
  rooted-tree witness type.

## Result
SUCCESS. The rooted-tree representation upgrade now includes a public Case B
normalization boundary, and `thm_301A_order5` consumes it in the reverse Case B
branch.

Verification run:
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/RootedTree.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderConditions.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build OpenMath.RootedTree OpenMath.OrderConditions`

All succeeded. `OrderConditions.lean` still emits pre-existing unused `simp`
argument warnings unrelated to this migration.

## Dead ends
The first `OrderConditions.lean` re-check failed with unknown identifiers for
the new Case B API because the rebuilt `RootedTree` interface had not yet been
picked up. Rebuilding `OpenMath.RootedTree` fixed the stale state; no proof
changes were needed.

## Discovery
The existing `BTree.OrderFiveBagWitness.caseB` payload was already sufficient
for theorem-side consumption once the `{1,1,2}` classifier was made public.
The remaining theorem-local Case B logic is now limited to tableau-specific
dispatch/target packaging, which matches the intended boundary.

## Suggested next approach
Continue the theorem-301A rooted-tree migration by checking whether any other
order-5 theorem-local normalization wrappers remain outside `RootedTree.lean`.
If none remain for Case B/C/D, the next cycle should focus on the next still
private tree-shape recovery boundary rather than tableau-specific dispatch code.

## Aristotle
Per the cycle strategy, there were no completed Aristotle results ready for
incorporation at the start of the cycle, and no fresh Aristotle batch was
submitted. This cycle did not introduce a new proof blocker requiring
Aristotle.
