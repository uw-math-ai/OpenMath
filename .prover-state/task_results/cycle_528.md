# Cycle 528 Results

## Worked on
Butcher §384 right-block convolution, in `OpenMath/ButcherGroup.lean`. Three
new theorems landed under the cycle 528 strategy:

1. `ButcherProduct.bWeighted_rightAuxAtCoef_leaf_eq` — the leaf base case
   of the `b`-weighted root sum, alias of the cycle 525
   `bWeighted_rightAuxAtCoef_leaf` packaged under the rotation-naming
   convention used by the node-side closures.
2. `ButcherProduct.bSeries_natAdd_leaf_eq` — leaf specialisation at
   `coef := t₁.bSeries`, collapsing the second-method `b`-weighted stage
   sum of the product tableau at `BTree.leaf` to `t₂.weightsSum`.
3. `ButcherProduct.bWeighted_rightAuxAtCoef_node_trunk_recursion` — the
   `S` ↔ `Sᶜ` reindexing of the cycle 526 powerset closed form
   `bWeighted_rightAuxAtCoef_node`. In this trunk-side form, `S` records
   cut children (cut factor `∏ p ∈ S, coef ...`) and `Sᶜ` records the
   children kept attached through the second-method `t₂.A`-twisted
   recursion.

## Approach
- Step 1: trivial `exact` from `bWeighted_rightAuxAtCoef_leaf`. No new
  computation needed; the cycle 525 lemma already gives `= t₂.weightsSum`,
  so the `_eq` companion is a one-line restatement.
- Step 2: rewrite by `bSeries_natAdd_eq_rightAuxAtCoef` (cycle 524) into
  the coefficient-parametric form, then by the cycle 525 leaf reduction
  `bWeighted_rightAuxAtCoef_leaf`. Two-line proof.
- Step 3: rewrite the LHS by the cycle 526 closed form
  `bWeighted_rightAuxAtCoef_node` (`Sᶜ`-cut, `S`-keep), unfold
  `Finset.powerset_univ`, and then reindex the universe `Finset (Fin
  children.length)` against itself via `Finset.sum_nbij'` with both
  bijection legs set to `S ↦ Sᶜ`. The two `compl_compl` round-trip checks
  and a single `rw [compl_compl]` close the integrand-equality side
  condition.

## Result
**SUCCESS.** `OpenMath/ButcherGroup.lean` compiles with no output via
`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean
OpenMath/ButcherGroup.lean`, no `sorry` markers (`rg -n "\bsorry\b"
OpenMath/ButcherGroup.lean` returns nothing), and `lake build
OpenMath.ButcherGroup` succeeds end-to-end.

## Dead ends
- Initial draft of step 3 used `Finset.sum_nbij'` with the lambda
  `fun S _ => Sᶜ` (curried with the membership proof). Lean 4 mathlib's
  `Finset.sum_nbij'` signature takes the bijection as `ι → κ` (no
  membership argument), so the call rejected with an "Application type
  mismatch" error. Switching to `fun S => Sᶜ` cleared it.
- Aristotle was not consulted this cycle, per the planner's standing
  cycle-528 directive (HTTP 429 has been the rule since cycle 511).

## Discovery
- The S/Sᶜ swap on a powerset over `Finset (Fin n)` is a clean two-line
  `Finset.sum_nbij'` reindex with both bijection legs equal to `compl`
  and both round-trip lemmas equal to `compl_compl`. This pattern will
  reappear when the §384 trunk recursion has to be matched against the
  Iserles / Butcher textbook forms, which conventionally name the kept
  side `S` (not `Sᶜ`).
- Step 1 is essentially a renaming. The cycle 525
  `bWeighted_rightAuxAtCoef_leaf` already had the `weightsSum` form,
  so the new `_eq` companion is a definitional alias. Worth keeping
  for symmetry with the node-side `_eq` and `_trunk_recursion` names.

## Suggested next approach
The next structural seam, recorded in `plan.md`, is the trunk-side
recursive decomposition that turns the *kept-side* product
`∏ p ∈ Sᶜ, ∑ j, t₂.A i j * rightAuxAtCoef t₂ coef (children.get p) j`
into something expressible purely in terms of `t₂.bSeries` values on
subtrees. Concrete sub-goals the next cycle should target, in order:

1. **Kept-leaf simplification.** When `children.get p = BTree.leaf`,
   the inner factor reduces to `∑ j, t₂.A i j * 1 = ∑ j, t₂.A i j`, and
   the `b`-weighted outer sum collapses to a row-of-`t₂.A` sum that
   equals `t₂.c`-style stage data. A focused lemma
   `bWeighted_rightAuxAtCoef_node_trunk_kept_leaf_eq` could pin this
   down for the all-leaves children list, mirroring step 1's
   leaf-base-case packaging.
2. **Kept-node `b`-pass-through.** When `children.get p = BTree.node gc`,
   the inner factor expands by `rightAuxAtCoef_node_eq_powerset_sum` and
   the `b`-weighted outer sum should descend through `Finset.sum_comm`
   into a powerset-of-grandchildren sum. The cycle 526 / 528 templates
   should transplant.
3. **Convolution identity at one-child trees.** Combining steps 1 and 2
   on `BTree.node [child]` gives a convolution closed form for the
   simplest non-leaf tree. This is the smallest non-trivial test bed
   for the honest §384 closed form and is a strict prerequisite for
   `QuotEquiv.bSeriesHom_product`.

The non-tautological tree convolution is still gated on these three
sub-goals; the cycle 512 / 516 blockers (`bSeriesConvolution`,
`IsG1Equiv.product_congr`, etc.) remain off-limits until the closed
form lands.
