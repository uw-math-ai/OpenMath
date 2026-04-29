# Cycle 569 Results

## Worked on
Butcher §384 / §386 bSeries-only convolution consistency in
`OpenMath/ButcherGroup/Section386Conv.lean`.

## Approach
Added the requested sorry-first scaffolds, verified the file compiled with
temporary sorries, then closed the concrete `node [node []]` case and the
parametric `BTree.node (List.replicate n (BTree.node []))` family.

The parametric proof mirrors cycle 568's leaf-family reindexing. The new
`innerCutForest_node_nil_cons` helper records that `node []` enumerates
the root-pruned choice before the kept-root choice. The new
`innerCutForest_replicate_node_nil_sum` reindexes those list choices to
the `Finset (Fin n)` powerset sum used by the existing §384 all-empty-node
closed form.

## Result
SUCCESS for steps 1 and 2:

- Closed `bSeriesConv_node_node_nil_consistency`.
- Closed `bSeriesConv_node_replicate_node_nil_consistency`.
- Verified `lake env lean OpenMath/ButcherGroup/Section386Conv.lean`.
- Verified `lake env lean OpenMath/ButcherGroup.lean`.

The full general `ButcherProduct.bSeriesConv_consistency` was not landed;
the temporary sorry-first theorem was removed before commit so no Lean file
contains a live `sorry`.

## Dead ends
Submitted the single remaining general theorem to Aristotle:

- Project: `acf8c051-c67d-43e4-b735-e0571dd2773a`
- File: `Section386Conv.lean`
- Status after the required 30-minute wait: `QUEUED`

No result was available to incorporate, and per the cycle policy I did not
keep polling.

The direct tree-induction attempt reduces with
`ButcherProduct.bSeries_eq_split` to

```lean
bSeriesConv α (t₂.bSeries) τ
  = ∑ i : Fin t, t₂.b i * ButcherProduct.convAt t₂ α τ i
```

but the node case needs a stagewise invariant before the final weighted
stage sum. `bSeriesConv` has already evaluated trunks by `t₂.bSeries`,
while `convAt_node` needs child-level terms at each stage.

## Discovery
The missing bridge should be a root-preserving cut sum evaluated against
`t₂.elementaryWeight _ i`, not immediately against `t₂.bSeries`. See
`.prover-state/issues/butcher_section386_general_consistency.md`.

## Suggested next approach
Define a local `cutAt α t₂ τ i` over root-preserving inner cuts weighted by
`t₂.elementaryWeight trunk i`, prove `cutAt_eq_convAt` by tree/list
induction using a generalized `innerCutForest` prefix invariant, then
derive the existing `bSeriesConv` identity by summing over `i` with
weights `t₂.b i`.
