# Cycle 505 Results

## Worked on
Butcher §387 raw integer powers of `ButcherProduct` and their lift to
`QuotEquiv` in `OpenMath/ButcherGroup.lean`.

## Approach
Added the recursive stage-count helper
`ButcherProduct.npowStages`, the right-associated raw power
`ButcherProduct.npow`, the quotient lift `QuotEquiv.npow`, computation
lemmas for zero/successor/one, the representative lemma
`QuotEquiv.npow_mk`, and the zero-power sanity lemmas
`QuotEquiv.bSeriesHom_npow_zero` and `QuotEquiv.weightsSum_npow_zero`.

Followed the sorry-first workflow: the scaffold with explicit `sorry`s
compiled with
`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean`.

Aristotle batch after scaffold:
- `ButcherTableau.ButcherProduct.npow_zero`:
  `170aa9c6-ee57-496f-b205-99920ca9bcb5` — `QUEUED`
- `ButcherTableau.ButcherProduct.npow_succ`:
  `07c51076-2e94-48aa-b0ab-aa46f85eeef7` — `QUEUED`
- `ButcherTableau.QuotEquiv.npow_mk`:
  `869eddf1-fb49-486d-a135-194012184c7c` — `QUEUED`
- `ButcherTableau.QuotEquiv.bSeriesHom_npow_zero`:
  `0d2ddea9-e47e-4743-aa69-07c79a6c4f11` — `QUEUED`
- `ButcherTableau.QuotEquiv.weightsSum_npow_zero`:
  `7329da44-d100-422a-a542-e952a6fd1976` — `QUEUED`

After the required `sleep 1800`, the single refresh still showed all five
jobs as `QUEUED`, so there were no Aristotle proofs to transplant.

## Result
SUCCESS. All new declarations are sorry-free and the file verifies.

Manual closures:
- The stage-count and raw/quotient zero/successor/one computation lemmas
  closed by `rfl`.
- `QuotEquiv.npow_mk` closed by induction on `n`; the successor case uses
  the induction hypothesis and `QuotEquiv.product_mk` by definitional
  reduction.
- `QuotEquiv.bSeriesHom_npow_zero` closed by `rfl`.
- `QuotEquiv.weightsSum_npow_zero` closed by simplifying the zero power to
  the zero-stage `trivialTableau`, reducing the weight sum to the empty
  `Fin 0` sum.

The right-associated orientation was load-bearing: the successor target has
stage count `ButcherProduct.npowStages s n + s`, exactly matching
`ButcherProduct (ButcherProduct.npow t n) t` and
`QuotEquiv.product (QuotEquiv.npow q n) q` by definitional equality.

## Dead ends
None. The blocked §384/§386 convolution path was not reopened.

## Discovery
The recursively defined stage count is enough for Lean to align the dependent
successor return types without an explicit transport. The zero-power
`weightsSum` sanity lemma does not need `trivialTableau_unique`; unfolding and
the empty `Fin 0` sum suffice.

## Suggested next approach
Keep §38 as the active target. The remaining §387 work is inverse and
non-trivial power behavior, but any `bSeriesHom` multiplicativity for powers
should wait for the blocked §384 convolution infrastructure.
