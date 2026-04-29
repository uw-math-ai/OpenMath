# Cycle 577 Results

## Worked on

Butcher §388 inverse-coefficient cancellation:

- canonical no-cut count in `BTree.innerCut` / `BTree.innerCutForest`;
- peeling lemma `bSeriesConv_eq_root_plus_nonRoot`;
- node-level inverse cancellation in `OpenMath/ButcherGroup.lean`.

## Approach

Started sorry-first in the two scheduled files and created the Aristotle
scaffold `.prover-state/aristotle_scaffolds/cycle_577/count_pair.lean`.
The single Aristotle submission returned HTTP 429 ("too many requests in
progress"), so no job was queued and the proof was completed manually.

The landed count proof follows the Path (1) mutual `List.countP` plan.
For node counts, I exposed a private forest-level copy of the strengthened
structural invariant, because the tree-level public theorem alone does not
identify the unique forest preimage of the no-cut node entry.

The peeling lemma converts the full and nonroot `filterMap` sums into list
sums, proves the pointwise full/nonroot/indicator decomposition, and uses
`innerCut_canon_count = 1` to peel exactly one `β τ` term.

## Result

SUCCESS.

- Added `bSeriesConvNonRoot` to `Section386Conv.lean` so the peeling lemma
  can live with the convolution infrastructure.
- Proved private `innerCut_canon_count` and
  `innerCutForest_canon_count`.
- Proved `bSeriesConv_eq_root_plus_nonRoot`.
- Proved `bSeriesConv_inverseCoeff_cancel_node` in the algebraic form
  forced by `inverseCoeff_node_eq`:
  `q.bSeries (node children) + bSeriesConv q.bSeries q.inverseCoeff (node children) = 0`.

## Dead ends

The planner's displayed Step 3 statement omitted the leading
`q.bSeries (BTree.node children)`.  That version does not follow from the
current recursion: peeling gives `inverseCoeff node + nonRoot`, while
`inverseCoeff_node_eq` cancels only
`q.bSeries node + nonRoot + inverseCoeff node`.

## Discovery

`lake env lean OpenMath/ButcherGroup.lean` uses the previously built olean
for imported modules.  After moving `bSeriesConvNonRoot` into
`Section386Conv.lean`, rebuilding `OpenMath.ButcherGroup.Section386Conv`
was necessary before the umbrella file saw the new declaration.

## Suggested next approach

Continue §388 with the symmetric convolution direction
(`q.inverseCoeff` as the first argument), then use the two cancellation
directions to define `G1.inv` and finish the `Group (G1 p)` instance.
