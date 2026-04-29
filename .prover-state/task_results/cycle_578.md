# Cycle 578 Results

## Worked on

§388 inverse left-cancellation (planner headline target):

```lean
theorem bSeriesConv_inverseCoeff_cancel_node_left
    {s : ℕ} (q : QuotEquiv s) (children : List BTree) :
    q.inverseCoeff (BTree.node children)
      + bSeriesConv q.inverseCoeff q.bSeries (BTree.node children) = 0
```

and the supporting `bSeriesConvNonRoot_inverseCoeff_swap` lemma in
`OpenMath/ButcherGroup/Section386Conv.lean`.

## Approach

Before scaffolding the strong induction, hand-evaluated the proposed
identity on small unit-stage tableaux to make sure the target was
sensible. It is not.

For 1-stage explicit Euler (`s = 1, b = (1), c = (0)`) at `τ = node [leaf]`:

```
q.inverseCoeff (node [leaf]) = 1
bSeriesConv q.inverseCoeff q.bSeries (node [leaf]) = 1
sum = 2 ≠ 0
```

For Heun (`s = 2, b = (1/2, 1/2), c = (0, 1)`) at `τ = node [leaf]`:

```
q.inverseCoeff (node [leaf]) = 1/2
bSeriesConv q.inverseCoeff q.bSeries (node [leaf]) = 3/2
sum = 2 ≠ 0
```

Both are unit-stage. The right-inverse identity (cycle 577 result) holds
at the same trees, e.g. `b + bSeriesConv b I = 1/2 + (-1/2) = 0` for
Heun.

The reduction in the planner's Step 3 is correct, so the failure of the
headline propagates to the proposed `bSeriesConvNonRoot` swap lemma.
Direct counterexample at `τ = node [leaf]`:

```
bSeriesConvNonRoot inverseCoeff τ (·=>bSeries·) =  +1
bSeriesConvNonRoot bSeries     τ (·=>inverseCoeff·) = -1
```

Once these counterexamples were in hand, abandoned the proof attempt and
followed the strategy's "If the strong induction stalls" clause:

- Landed the sorry-free leaf companion
  `bSeriesConv_inverseCoeff_cancel_leaf_left` in
  `OpenMath/ButcherGroup.lean` (a one-line corollary of
  `bSeriesConv_leaf`).
- Wrote a focused issue file
  `.prover-state/issues/butcher_section388_left_cancellation.md`
  documenting the failed identity, both counterexamples, and the
  structural reason (the `inverseCoeff leaf = 1` augmentation prevents
  `inverseCoeff` from being a true convolution inverse — even at the
  leaf, `bSeriesConv b I leaf = I leaf = 1 ≠ 0`).

No `sorry` was introduced into tracked code, transient or otherwise.

## Result

PARTIAL.

- Landed `bSeriesConv_inverseCoeff_cancel_leaf_left` (true, trivial
  rewrite of `bSeriesConv_leaf`).
- Landed
  `.prover-state/issues/butcher_section388_left_cancellation.md`
  documenting why the planner's headline target is mathematically
  false.
- Verified `lake env lean OpenMath/ButcherGroup.lean` (the umbrella file
  with the new theorem) compiles without errors.

The originally scheduled cancellation theorem and its swap lemma were
not landed — they are not theorems.

## Dead ends

- The planner's "Step 2 strong induction" approach. The IH cannot be
  applied "inside a summand" because each summand of
  `bSeriesConvNonRoot α τ β` is a scalar `(∏ α(σᵢ)) · β(trunk)`, with
  the σᵢ ranging over distinct cut subtrees; the swap is not a
  per-cut equation.
- The "right-inverse implies left-inverse" Hopf-algebraic argument.
  This would require `inverseCoeff` to be a true two-sided convolution
  inverse, which it is not — already at the leaf,
  `b leaf + bSeriesConv b I leaf = b leaf + 1 ≠ 0` in general. The
  current `inverseCoeff` is a *partial* recursion that satisfies the
  cancellation only on non-leaf trees and is the §388 textbook artifact,
  not the convolution inverse.

## Discovery

The §388 `inverseCoeff` recursion as currently defined produces a partial
right-inverse (cancelling only at non-leaf trees), not a two-sided
convolution inverse. In particular `inverseCoeff leaf = 1` for every
`q`, while a true convolution right-inverse would require
`inverseCoeff leaf = -q.bSeries leaf`. The §388 textbook statement
(cycle 575) is consistent with this partial recursion; the eventual
`G1.inv` group instance is **not** — it cannot be derived purely from
the `inverseCoeff` function and instead requires a tableau-level
construction (e.g. the standard Butcher antipode realised as a
`QuotEquiv s'`).

## Suggested next approach

For the planner:

1. Re-scope §388 to the right-direction cancellation alone (cycle 577
   result), and stop trying to extract a left-direction identity from
   the `inverseCoeff` recursion.
2. For the `Group (G1 p)` instance, plan a separate construction:
   build a tableau-level antipode `qInv : QuotEquiv s'` for each unit-
   stage `q`, prove `IsG1Equiv p (q.product qInv)
   (Quotient.mk _ trivialTableau)` and its symmetric counterpart, and
   define `G1.inv` from there. The cycle 575–577 `inverseCoeff`
   infrastructure becomes a §388 textbook artifact rather than a tool
   in the group construction.
3. Optionally prove convolution associativity for arbitrary
   `α, β, γ : BTree → ℝ` in `Section386Conv.lean` (a long but feasible
   combinatorial induction on cut structure) so that future inverse
   uniqueness arguments can use the standard
   `S = S * (id * R) = R` line.

## Files changed

- `OpenMath/ButcherGroup.lean`: added
  `bSeriesConv_inverseCoeff_cancel_leaf_left` (sorry-free).
- `.prover-state/issues/butcher_section388_left_cancellation.md`:
  new issue file with two unit-stage counterexamples.
- `.prover-state/task_results/cycle_578.md`: this file.
