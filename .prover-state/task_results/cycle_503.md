# Cycle 503 Results

## Worked on

Butcher §384 identity-prep for the quotient-facing Butcher-series map in
`OpenMath/ButcherGroup.lean`.

## Approach

Followed the sorry-first and Aristotle-first workflow. Added the raw
zero-stage identity statements for the b-weighted elementary-weight sum,
their `QuotEquiv` lifts, the §384-facing `QuotEquiv.bSeriesHom` wrapper,
and two small identity/associativity lemmas.

Submitted six Aristotle jobs against the live scaffold, then waited 30
minutes before checking once:

- `50a8a51a-5f33-48b6-afe5-b823226a5626`:
  `ButcherProduct.bSeries_one_left` — `COMPLETE`
- `d0a9df30-d8f4-4b59-a69e-5b0cfdbd2977`:
  `ButcherProduct.bSeries_one_right` — `COMPLETE`
- `0d7e5bd5-90de-4f57-af0f-569a2bf4cc76`:
  `QuotEquiv.product_bSeries_one_left` — `COMPLETE`
- `a3301df9-e63f-4e5e-99a4-33f9222dbfcc`:
  `QuotEquiv.product_bSeries_one_right` — `COMPLETE`
- `2558be17-11b6-4598-9d6e-ff4e95cdd19e`:
  `QuotEquiv.bSeriesHom_one` — `COMPLETE_WITH_ERRORS`
- `e14a1c2b-b091-4e8b-bd13-5e8c1fa2e9ac`:
  `QuotEquiv.bSeriesHom_assoc` — `COMPLETE`

Used the Aristotle quotient-lift proofs directly in shape, but rewrote the
raw one-sided identity proofs by hand using the live cross-size helper
`elementaryWeight_eq_of_A`, `finCongr (Nat.zero_add t)`, and
`finCongr (Nat.add_zero s)`.

## Result

SUCCESS. Landed sorry-free declarations:

- `ButcherProduct.bSeries_one_left`
- `ButcherProduct.bSeries_one_right`
- `QuotEquiv.product_bSeries_one_left`
- `QuotEquiv.product_bSeries_one_right`
- `QuotEquiv.bSeriesHom`
- `QuotEquiv.bSeriesHom_one`
- `QuotEquiv.bSeriesHom_assoc`

Verification:

- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build`
- `rg -n "sorry|admit" OpenMath/ButcherGroup.lean` found no matches.

Also updated `plan.md` and opened
`.prover-state/issues/butcher_section384_convolution.md` for the remaining
tree-indexed product/convolution needed by `QuotEquiv.bSeriesHom_product`.

## Dead ends

The first manual proof tried to close the raw block compatibility facts with
a single `simp [ButcherProduct, trivialTableau]`. That did not reduce
arbitrary indices of type `Fin (0+t)` / `Fin (s+0)` enough. Explicit
`Fin.addCases` splits made the empty block disappear, after which
`elementaryWeight_eq_of_A` supplied the recursive elementary-weight equality.

The §384 convolution statement was not added. A tautological definition in
terms of `QuotEquiv.product` would compile but would not express Butcher's
tree-coefficient product.

## Discovery

The one-sided identity laws only need `A` and `b`, so they are unaffected by
the known `c`-field mismatch in `ButcherProduct` associativity.

For the honest product formula, the second stage block expands at each node
as a list-fold product of sums: lower-left completed-child contributions from
`t₁.bSeries` plus lower-right recursive contributions from `t₂.A`. This
points to a list-subset expansion lemma for
`children.foldr (fun child acc => acc * (x child + y child)) 1`.

## Suggested next approach

Define the Butcher §386-style recursive product on tree-indexed coefficients
first, preferably via list-split/subset infrastructure matching the current
`elementaryWeight` `List.foldr`. Then prove the headline
`QuotEquiv.bSeriesHom_product` against that explicit product.
