# Cycle 527 Results

## Worked on

Butcher §384 right-block convolution in `OpenMath/ButcherGroup.lean`,
specifically the coefficient-parametric two-level expansion of
`rightAuxAtCoef` and its `b`-weighted specialization.

## Approach

Followed the cycle 522 and cycle 525 proof templates.

1. Added the sorry-first statements for:
   - `ButcherProduct.rightAuxAtCoef_node_two_level_eq_powerset_sum`
   - `ButcherProduct.bWeighted_rightAuxAtCoef_node_two_level`
   - `ButcherProduct.bSeries_natAdd_node_two_level_eq_rightAuxAtCoef`
2. Verified the statements typechecked with Lean, then closed the holes
   manually. The unweighted theorem is the direct cycle 522 transplant:
   rewrite by `rightAuxAtCoef_node_eq_powerset_sum`, use
   `Finset.sum_congr`/`Finset.prod_congr`, case-split each kept child,
   simplify leaves by `rightAuxAtCoef_leaf`, and unfold node children by
   `rightAuxAtCoef_node_eq_powerset_sum`.
3. Derived the weighted theorem with the same `cut`/`kept` abbreviations,
   `Finset.mul_sum`, `Finset.sum_comm`, and `ring` chain as the existing
   weighted node lemmas.
4. Specialized with `coef := t₁.bSeries` by rewriting through
   `ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef` and the new weighted
   coefficient-parametric theorem.

## Result

SUCCESS - the three planned cycle-527 theorems landed sorry-free:

- `ButcherProduct.rightAuxAtCoef_node_two_level_eq_powerset_sum`
- `ButcherProduct.bWeighted_rightAuxAtCoef_node_two_level`
- `ButcherProduct.bSeries_natAdd_node_two_level_eq_rightAuxAtCoef`

`plan.md` was updated in both the §384 ledger and `## Current Target`.

Verification:

- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean`
  succeeded with no output.
- `rg -n "\bsorry\b" OpenMath/ButcherGroup.lean` returned no matches.
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.ButcherGroup`
  succeeded (8029/8029), with only pre-existing `OpenMath.OrderConditions`
  warnings/infos.

## Aristotle status

Not used. The cycle-527 strategy explicitly said not to submit Aristotle at
the start because recent cycles hit HTTP 429 / queued failures, and to use at
most one batch only if the two-level proof stalled. The cycle 522 / 525
templates transplanted directly, so no batch was needed.

## Dead ends

No proof dead ends. The only deliberate detour was the required sorry-first
typecheck: Lean accepted the three new statements with the expected
`declaration uses sorry` warnings before the holes were closed.

No `QuotEquiv.bSeriesHom_product` scaffold was committed. The next statement
still needs the honest `(trunk, cuts)` coefficient product; adding a
tautological product definition would repeat the cycle 512 failure mode.

## Discovery

The coefficient-parametric two-level proof is a literal structural mirror of
cycle 522. No extra reindexing is needed on the `rightAuxAtCoef` side because
cycle 526's `rightAuxAtCoef_node_eq_powerset_sum` already presents the cut
factor over `Sᶜ` and the kept factor over `S`.

## Suggested next approach

Define the general `(trunk, cuts)` closed form for
`∑ i, t₂.b i * ButcherProduct.rightAuxAtCoef t₂ coef τ i`, likely by adding
a recursive tree/forest decomposition that records the second-method trunk
and the coefficient-side cuts. Once that expression mentions the inputs only
through `coef` and `t₂.bSeries`, the natural next headline is the honest
`QuotEquiv.bSeriesHom_product` theorem.
