# Cycle 583 Results

## Worked on

Butcher §386 augmented convolution planning scaffold for
`OpenMath/ButcherGroup/Section386Aug.lean`, targeting the §388 antipode
path.

## Approach

Built the requested sorry-first `AugSeries` / `bSeriesConvAug` scaffold,
using the existing `BTree.innerCut` list and adding the full-prune branch
weighted by `β.emptyVal`.  The scaffold initially compiled with the intended
temporary sorries.

Prepared five Aristotle inputs in
`.prover-state/aristotle_scaffolds/cycle_583/`:

- `bSeriesConvAug_leaf.lean`
- `bSeriesConvAug_node_nil.lean`
- `bSeriesConvAug_node_singleton_leaf.lean`
- `bSeriesConv_eq_bSeriesConvAug_zero_emptyVal.lean`
- `AugSeries_mul_assoc_at_leaf.lean`

## Result

FAILED — the requested arbitrary-`AugSeries`
`mul_assoc_at_node_singleton_leaf` sanity check is false under the concrete
cycle 583 definition.

The tracked partial `OpenMath/ButcherGroup/Section386Aug.lean` scaffold was
removed, per the strategy's blocker instruction.  The obstruction is
recorded in
`.prover-state/issues/butcher_section386_aug_middle_emptyval.md`.

## Aristotle usage

All five scaffold submissions returned HTTP 429 immediately:

```text
You have too many requests in progress. Please cancel or wait for a project
to complete before starting a new one.
```

No Aristotle project IDs were accepted, so there was no 30-minute wait or
polling step to perform.  The finite closed forms were then attempted
manually.

## Dead ends

- `bSeriesConvAug_leaf` and `bSeriesConvAug_node_nil` close by direct
  unfolding; `node []` needs `ring` after `simp` because the full-prune cut
  appears before the trivial cut in `innerCut_node_nil`.
- `bSeriesConvAug_node_singleton_leaf` closes after unfolding, but the
  natural sum order is
  `α (node [leaf]) * β.emptyVal + (β (node [leaf]) + α leaf * β (node []))`;
  normalization is needed to match the displayed three-term form.
- The depth-2 associativity proof does not fail because of tactic search.
  After unfolding the closed forms, the left side has the term
  `β.emptyVal * α leaf * γ (node [])`; the right side has
  `α leaf * γ (node [])`.  These are equal only when the middle empty value
  is `1`.

## Discovery

The chosen empty-forest convention is still the right convention for
ordinary B-series: `AugSeries.ofTree β = ⟨1, β⟩`, so canonical augmented
series are unital.  The problem is that the proposed `AugSeries` type admits
arbitrary `emptyVal`, while the proposed convolution only uses the right
empty value on the full-prune branch and does not use the left empty value
on the trivial no-prune branch.  Thus arbitrary associativity is too strong.

The old-convolution bridge also exposed the asymmetry: the proposed
`bSeriesConv_eq_bSeriesConvAug_zero_emptyVal` uses `⟨0, α⟩` on the left only
because the definition ignores `α.emptyVal` on `some trunk` branches.  A
fully symmetric arbitrary-empty convolution would instead recover the old
definition with left empty value `1` and right empty value `0`.

## Suggested next approach

Re-run the augmented-module cycle with one design correction before proving
general associativity: either restrict the multiplication theorem to unital
augmented series (`emptyVal = 1`) or enrich the cut representation so the
trivial no-prune branch is explicitly weighted by `α.emptyVal`.  The unital
restriction is the smaller change and preserves the intended
`AugSeries.ofTree` convention.
