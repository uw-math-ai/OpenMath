# Cycle 575 Results

## Worked on

Butcher §388 inverse construction, first layer only:

- raw augmentation predicate `ButcherTableau.QuotEquiv.IsUnit`
- guarded quotient predicate `ButcherTableau.G1.IsUnit`
- proper/non-root cut helper `ButcherTableau.bSeriesConvNonRoot`
- recursive inverse coefficients `ButcherTableau.QuotEquiv.inverseCoeff`
- leaf sanity lemma `ButcherTableau.QuotEquiv.inverseCoeff_leaf`

All tracked Lean edits stayed in `OpenMath/ButcherGroup.lean`.

## Approach

The unit predicate on `QuotEquiv` is the direct augmentation condition
`q.bSeries BTree.leaf = 1`.  The `G1` lift is guarded by `hp : 1 ≤ p`
and defined through the existing order-restricted coefficient map:
`G1.bSeriesHomAt p BTree.leaf ... g = 1`.  The representative lemma
`G1.isUnit_mk_iff` closes by reducing `bSeriesHomAt_mk` and
`QuotEquiv.bSeriesHom`.

For the inverse recursion, I introduced
`bSeriesConvNonRoot α τ βBelow`, where `βBelow` is only available on
trunks `σ` with `σ.order < τ.order`.  The helper filters the existing
`BTree.innerCut` enumeration and contributes `0` for the no-cut trunk,
which has the same order as `τ`.  This lets `QuotEquiv.inverseCoeff`
terminate by `τ.order`; the recursive call is exactly justified by the
smaller-order witness passed to `βBelow`.

## Result

SUCCESS.

- `lake env lean OpenMath/ButcherGroup.lean` exits 0.
- `lake build OpenMath.ButcherGroup` exits 0.
- `lean_verify` on `QuotEquiv.inverseCoeff_leaf` and
  `G1.isUnit_mk_iff` reports only the ambient quotient axioms
  `{propext, Classical.choice, Quot.sound}` and no warnings.
- `OpenMath/ButcherGroup.lean` is 2923 lines, still below the 3000-line
  cap.
- `plan.md` now records cycle 575 and marks §388 in progress.

## Dead ends

- Aristotle: I created the focused scaffold
  `.prover-state/aristotle_scaffolds/cycle_575/inverseCoeff_termination.lean`
  and submitted it first.  Aristotle returned HTTP 429
  ("too many requests in progress") before a project id was created.  Per
  strategy, I did not retry or submit the second planned job.
- A separate unit-lift scaffold would have needed the modified umbrella
  module available as a rebuilt import, so I removed it and closed the
  one-line proof manually.

## Discovery

- Passing the whole recursive function into `bSeriesConv` would hide the
  recursive calls from Lean's termination checker.  The successful shape
  is to make the proper-cut helper depend on
  `∀ σ, σ.order < τ.order → ℝ`; then the recursive call's decreasing proof
  is the helper's argument.
- Because the recursion is compiled as a well-founded recursion on
  `BTree.order`, the leaf sanity lemma is not definitionally `rfl`; it
  closes by `rw [inverseCoeff]`.

## Suggested next approach

Cycle 576 should stay on §388 without attempting a `Group` instance:

1. Prove a peeling lemma relating the existing `bSeriesConv α β τ` to
   `β τ + bSeriesConvNonRoot α τ (fun σ _ => β σ)`.
2. Use that lemma to state the non-leaf Möbius cancellation equation for
   `QuotEquiv.inverseCoeff`.
3. Add the first product-side sanity theorem specialized to
   `q.bSeries` and `q.inverseCoeff`, but stop before defining `G1.inv`.
4. If the leaf normalization creates a mismatch with the current
   zero-stage identity convention, write a focused issue before changing
   definitions.
