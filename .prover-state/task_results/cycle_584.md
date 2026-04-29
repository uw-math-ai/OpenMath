# Cycle 584 Results

## Worked on

§386 unital augmented convolution. New tracked module
`OpenMath/ButcherGroup/Section386Aug.lean`, re-exported from
`OpenMath/ButcherGroup.lean`. Lands the cycle 583 issue's recommended
fix path: keep the augmented `bSeriesConvAug` definition, restrict the
multiplication theorem to unital augmented series via
`AugSeries.IsUnital`.

## Approach

Sorry-first scaffold per CLAUDE.md, then closed each sorry directly
from the actual `BTree.innerCut` / `BTree.innerCutForest` clauses in
`Section386Conv.lean`.

Closed forms reduce by `simp [bSeriesConvAug, BTree.innerCut,
BTree.innerCutForest]`. The singleton-leaf form additionally needed
`add_assoc` to normalize the parenthesisation.

Bridge `bSeriesConv α β τ = bSeriesConvAug ⟨1, α⟩ ⟨0, β⟩ τ` proved by
list induction on `τ.innerCut α`. The asymmetric `bSeriesConv` uses
`filterMap` so the `none` branch contributes nothing; the augmented
form uses `map` so the `none` branch contributes `c.2 * 0 = 0`.
Branch-by-branch list induction with `rw [mul_zero, zero_add]` on the
none branch closes the equality of sums without disturbing the IH's
unfolded RHS.

Headline `mul_assoc_at_node_singleton_leaf` reduces to a `ring` after
unfolding the closed forms and substituting the unital hypotheses
`hβ : β.emptyVal = 1`, `hγ : γ.emptyVal = 1`. (The `α.emptyVal`
hypothesis is not used by the proof but is kept in the statement
per the strategy's signature.)

Aristotle: prepared one scaffold under
`.prover-state/aristotle_scaffolds/cycle_584/mul_assoc_singleton_leaf.lean`
covering all five targets and submitted it. Returned HTTP 429
immediately, matching the documented baseline of cycles 509 / 511 /
512 / 515 / 517 / 521 / 539 / 551 / 575 / 579 / 583. Per strategy,
did not retry-spam; closed manually.

## Result

SUCCESS.

`OpenMath/ButcherGroup/Section386Aug.lean` and the umbrella
`OpenMath/ButcherGroup.lean` build cleanly via `lake env lean`.
Targets landed:
- `AugSeries` (structure with `emptyVal : ℝ`, `toFun : BTree → ℝ`)
- `AugSeries.IsUnital` (`emptyVal = 1`)
- `bSeriesConvAug` (full inner-cut sum, both branches contribute)
- `bSeriesConvAug_leaf`
- `bSeriesConvAug_node_nil`
- `bSeriesConvAug_node_singleton_leaf`
- `bSeriesConv_eq_bSeriesConvAug` (bridge, right `emptyVal = 0`)
- `mul_assoc_at_node_singleton_leaf` (depth-2, unital)
- `mul_assoc_at_leaf` / `mul_assoc_at_node_nil` (corollaries)

## Dead ends

Initial bridge attempt used `congr 1` to reduce the `.sum = .sum`
equality to a list-level equality. That fails: the asymmetric form's
`filterMap` drops `none` entries entirely, while the augmented form's
`map` keeps them with weight `c.2 * 0`. The lists are not pointwise
equal, only their sums.

A second attempt used `simp only [..., mul_zero, zero_add]` over the
whole goal. `mul_zero` rewrites `c.2 * 0` inside the lambda to `0`,
which mutates the goal but not the IH, leaving them out of sync.
Replaced with a hand `rw [mul_zero, zero_add]` on just the head term
(after `List.sum_cons` exposed it), keeping the tail's lambda intact
for `exact ih`.

## Discovery

`α.emptyVal` is not used by `bSeriesConvAug α β τ` for any `τ` —
only `α.toFun`, `β.emptyVal`, and `β.toFun` appear. So unitality of
the *left* argument is not actually required for any of the depth-2
sanity checks; only `β.emptyVal = 1` and `γ.emptyVal = 1` matter.
The strategy's three-hypothesis statement is preserved for surface
uniformity, but the proof discharges `α.IsUnital` as `_`.

The bridge `bSeriesConv α β τ = bSeriesConvAug ⟨1, α⟩ ⟨0, β⟩ τ` is
asymmetric in exactly the way the cycle 580 counterexample
identified: zero `emptyVal` on the right matches `bSeriesConv`'s
filtering of the full-prune branch.

## Suggested next approach

Lift the unital depth-2 associativity to **all trees** by `BTree.rec`.
The induction step needs a list-level reindexing combinator on
`BTree.innerCutForest`, which is the same family of combinators as
the cycle 569 / 570 reindexing. Concretely, the planner should set up
a sorry-first
`bSeriesConvAug_assoc (α β γ : AugSeries)
    (hβ : β.IsUnital) (hγ : γ.IsUnital) (τ : BTree) :
    bSeriesConvAug ⟨1, fun σ => bSeriesConvAug α β σ⟩ γ τ =
      bSeriesConvAug α ⟨1, fun σ => bSeriesConvAug β γ σ⟩ τ`
and the helper
`bSeriesConvAug_node (α β : AugSeries) (children : List BTree) : ...`
that exposes the trunk-keep / trunk-prune split symmetrically.

Once unital associativity at all trees lands, the §388 antipode work
can define `G1.inv` via inverse `AugSeries` recursion on tree order
(similar to `QuotEquiv.inverseCoeff` but using `bSeriesConvAug`'s
symmetric framework rather than the asymmetric `bSeriesConv` that
cycle 578 disproved).
