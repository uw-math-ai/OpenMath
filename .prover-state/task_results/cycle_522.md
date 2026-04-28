# Cycle 522 Results

## Worked on

Butcher §384 right-block two-level expansion in
`OpenMath/ButcherGroup.lean`, immediately after the cycle 521 powerset
lemmas.

Added:
- `ButcherProduct.rightAuxAt_node_two_level_eq_powerset_sum`
- `ButcherProduct.bSeries_natAdd_node_two_level_eq_powerset_sum`

Both extend the `rightAuxAt` / `bSeries_natAdd` chain by case-splitting
each kept child's contribution into a leaf branch (`∑ j, t₂.A i j`) or a
node branch (the inner `(cut, kept)` powerset sum at the new parent
index `j`).

## Approach

1. Added both theorem statements with `:= by sorry` immediately before
   `namespace QuotEquiv` and verified
   `OpenMath/ButcherGroup.lean` compiled with exactly two new `sorry`
   warnings and no other tracked sorries.
2. Skipped Aristotle this cycle: the strategy explicitly notes recent
   cycles 509/511–513/515/517/519/521 returned HTTP 429 immediately, and
   the proofs at hand were close enough to the cycle 521 templates that
   manual closure was the cheaper path.
3. Closed Deliverable 1
   (`rightAuxAt_node_two_level_eq_powerset_sum`) by:
   - rewriting with `ButcherProduct.rightAuxAt_node_eq_powerset_sum` to
     reach the cycle 521 powerset form,
   - applying `Finset.sum_congr` over the kept set `S`, then `congr 1`
     and `Finset.prod_congr` over kept indices `p ∈ S`,
   - generalising `children.get p` to a fresh local `c : BTree` and
     case-splitting on `c` with `cases c with | leaf | node gc`,
   - the leaf case reduces by `simp [ButcherProduct.rightAuxAt_leaf]`
     (using `mul_one` to collapse `∑ j, t₂.A i j * 1`),
   - the node case reduces by `Finset.sum_congr` plus another rewrite
     with `ButcherProduct.rightAuxAt_node_eq_powerset_sum` at the
     subtree.
4. Closed Deliverable 2
   (`bSeries_natAdd_node_two_level_eq_powerset_sum`) by reusing the
   cycle 521 distribution pattern from
   `bSeries_natAdd_node_eq_powerset_sum`: introduced local `cut S` and
   `kept i S` abbreviations matching the new two-level kept factor,
   distributed `∑ i, t₂.b i * (...)` through `Finset.mul_sum`, swapped
   sums with `Finset.sum_comm`, factored `cut S` out of the inner
   `Fin t` sum by `ring`, and re-expanded the abbreviations with
   `simp [cut, kept]`.

## Result

SUCCESS — both concrete deliverables landed with zero tracked `sorry`s.

Verification:
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH \
   lake env lean OpenMath/ButcherGroup.lean` succeeded.
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH \
   lake build OpenMath.ButcherGroup` succeeded; only pre-existing
  `OrderConditions.lean` `ring` info messages were emitted, no errors.
- `grep -c sorry OpenMath/ButcherGroup.lean` returned `0`.

`plan.md` now records both new theorem names under §384 in the chapter
ledger and in the `## Current Target` body. §384 remains active per the
strategy.

## Aristotle outcome

Did not submit this cycle. The strategy permitted skipping retries on
429 and recommended manual closure when the proofs are templated off
existing cycles. Recent cycle 521 already submitted once and got 429.
Skipping the round-trip saved time without giving up any cycle 522
deliverables.

## Dead ends

None. The proofs followed the cycle 521 templates closely. The only
non-obvious trick was using `generalize children.get p = c` before the
`cases` so that the match on the LHS and RHS reduce simultaneously
when `c` is replaced by `.leaf` or `.node gc` — without the
generalisation, `cases` on `children.get p` directly would not rewrite
the RHS match expression.

## Discovery

The two-level form is structurally a pure rewriting of the cycle 521
powerset sum: when you generalise `children.get p`, the kept-side
factor and the match expression on the RHS are definitionally equal at
each `BTree` constructor (modulo `rightAuxAt_leaf` and
`rightAuxAt_node_eq_powerset_sum`). This means the next layer can be
done by literally the same template at one more depth, except the
inner powerset sum's index type now depends on which node was kept —
so any further unfolding has to happen *after* a closed `(trunk, cuts)`
combinator over `BTree` is in place, not before.

## Suggested next approach

Define an honest closed-form `(trunk, cuts)` combinator over `BTree`
— e.g. a structural recursion `convolutionAux : ButcherTableau s →
ButcherTableau t → BTree → ℝ` that, on `node children`, sums over
subsets `S` of `children`, multiplying the cut-side `t₁.bSeries` factor
by an inner `t₂.bSeries`-weighted term computed from a fresh `BTree`
built out of the kept subtrees — and prove it equals
`∑ i, t₂.b i * rightAuxAt t₁ t₂ τ i` by structural induction on `τ`,
using
`bSeries_natAdd_node_two_level_eq_powerset_sum` as the node step. That
should finally unblock `QuotEquiv.bSeriesHom_product` and the
downstream `IsG1Equiv.product_congr` / `G1.mul` chain.
