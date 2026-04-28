# Cycle 501 Results

## Worked on
Butcher section 382 quotient lift for raw RK composition in
`OpenMath/ButcherGroup.lean`.

## Approach
Followed the strategy:

1. Added the sorry-first surface for
   `ButcherProduct.equiv_congr`, `QuotEquiv.product`,
   `QuotEquiv.product_mk`, and `QuotEquiv.product_weightsSum`.
2. Verified the sorry-first file compiled.
3. Submitted five Aristotle jobs and ran the required `sleep 1800` before
   checking statuses.
4. Closed the live proofs manually while Aristotle ran.

`ButcherProduct.equiv_congr` uses the block permutation
`finSumFinEquiv.symm.trans ((Equiv.sumCongr sigma1 sigma2).trans finSumFinEquiv)`.
The `A`, `b`, and `c` component equations split with `Fin.addCases`; each
branch then reduces by `simp [sigma, ButcherProduct]` to either the appropriate
relabeling hypothesis, `0 = 0`, or the lower-left broadcast weight equation.

`QuotEquiv.product` is a direct `Quotient.lift2` using
`ButcherProduct.equiv_congr` as the well-definedness witness.
`product_mk` is `rfl`. `product_weightsSum` uses
`Quotient.inductionOn2` and `butcherProduct_b_sum`.

## Result
SUCCESS.

- Added `ButcherProduct.equiv_congr`.
- Added `QuotEquiv.product`.
- Added `QuotEquiv.product_mk`.
- Added `QuotEquiv.product_weightsSum`.
- Updated `plan.md` so section 382 records the quotient lift and points the next
  step at associativity on `QuotEquiv`.

`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean`
exits 0.

Lean LSP `lean_verify` on
`ButcherTableau.ButcherProduct.equiv_congr` and
`ButcherTableau.QuotEquiv.product_weightsSum` reported only the expected
quotient/classical axioms (`propext`, `Classical.choice`, `Quot.sound`) and
no suspicious-source warnings.

## Aristotle
Submitted batch:

1. `0cbbaa6f-f6c1-44a7-95e4-a4432de60813`
   (`equiv_congr_full.lean`) - `COMPLETE`.
2. `1665a8a7-16d8-49b9-9445-e7c58f60a699`
   (`a_cast_cast.lean`) - `COMPLETE`.
3. `10ec92ca-7c88-46f5-a932-a06177f8ad78`
   (`product_lift_mk.lean`) - `COMPLETE`.
4. `fba3418b-5c47-43ef-9573-d62f66e17987`
   (`product_weights_sum.lean`) - `COMPLETE`.
5. `9fa101c1-3f54-428d-9bed-dfad3a0ede24`
   (`product_assoc_scratch.lean`) - `COMPLETE`.

Downloaded outputs under
`.prover-state/aristotle_scaffolds/cycle_501/results/`. Several Aristotle
outputs created stub/replacement `OpenMath.ButcherGroup.lean` files because
the remote project did not have the live dependency graph, so I did not
transplant them. The useful confirmations were:

- `product_mk` is definitional (`rfl`).
- the upper-left `A` branch is `simp [ButcherProduct]` followed by the
  relabeling hypothesis.
- the weights proof should be quotient representative induction plus the
  product sum lemma.
- associativity should use the natural reassociation equivalence
  `finCongr (Nat.add_assoc s t u).symm` / `Fin.cast`, but this was not part
  of the cycle deliverable.

## Dead ends
No Lean dead ends. The only Aristotle limitation was the recurring stubbed
dependency issue, so the live manual proof was preferred.

## Discovery
The block permutation route is much lighter than expected: the existing
`Fin.addCases` and `finSumFinEquiv` simp lemmas reduce all four matrix
branches without needing custom helper lemmas.

A broad `rg -n "sorry" OpenMath/` still finds pre-existing prose comments
in unrelated files, but `OpenMath/ButcherGroup.lean` has no live or textual
`sorry` occurrences.

## Suggested next approach
Cycle 502 should prove quotient associativity. The likely witness is the
stage reassociation permutation induced by
`finCongr (Nat.add_assoc s t u).symm`, with a component-wise proof following
the same `Fin.addCases` block-reduction style as `ButcherProduct.equiv_congr`.
