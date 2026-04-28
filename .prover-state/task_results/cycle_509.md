# Cycle 509 Results

## Worked on

Butcher §387 closed-form arithmetic in `OpenMath/ButcherGroup.lean`:

- `ButcherProduct.npowStages_add`
- `QuotEquiv.weightsSum_npow_add`
- `QuotEquiv.cSum_npow_add`
- `QuotEquiv.weightsSum_npow_three`
- `QuotEquiv.cSum_npow_three`

## Approach

Added the five target declarations sorry-first and verified the file compiled
with exactly five expected `sorry` warnings. Then attempted to submit all five
targets to Aristotle against the live `OpenMath/ButcherGroup.lean` file, one
prompt per theorem:

- `ButcherTableau.ButcherProduct.npowStages_add`: HTTP 429, too many requests
  in progress
- `ButcherTableau.QuotEquiv.weightsSum_npow_add`: HTTP 429, too many requests
  in progress
- `ButcherTableau.QuotEquiv.cSum_npow_add`: HTTP 429, too many requests in
  progress
- `ButcherTableau.QuotEquiv.weightsSum_npow_three`: HTTP 429, too many
  requests in progress
- `ButcherTableau.QuotEquiv.cSum_npow_three`: HTTP 429, too many requests in
  progress

Because no Aristotle jobs were accepted, there were no project IDs to poll or
proofs to transplant. After the 30-minute wait, a single Aristotle queue check
showed only older queued jobs from cycles 505-508; no cycle-509 project was
created. During the wait window, closed the targets manually:

- `npowStages_add`: rewrite through `npowStages_eq` and use `Nat.add_mul`.
- `weightsSum_npow_add`: instantiate `weightsSum_npow` at `m+n`, `m`, and `n`;
  `push_cast` and `linarith`.
- `cSum_npow_add`: instantiate `cSum_npow` at `m+n`, `m`, and `n`;
  `push_cast` and `nlinarith` for the quadratic cross term.
- `weightsSum_npow_three`: direct `simpa` from `weightsSum_npow q 3`.
- `cSum_npow_three`: instantiate `cSum_npow q 3`, `push_cast`, then
  `linarith`.

## Result

SUCCESS. All five target lemmas are sorry-free. The §387 plan ledger was
updated without rotating `## Current Target`.

Verification:

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH \
  lake env lean OpenMath/ButcherGroup.lean
rg -n "sorry" OpenMath/ButcherGroup.lean
```

`lake env lean` returned no output, and `rg` found no `sorry`s.

Lean LSP verification:

- `ButcherTableau.QuotEquiv.cSum_npow_add`: no source-scan warnings; axioms
  `propext`, `Classical.choice`, `Quot.sound`.
- `ButcherTableau.ButcherProduct.npowStages_add`: axioms `propext`.

## Dead ends

Aristotle could not accept any of the five jobs because the in-flight request
cap was already full. This matches the recent queue-pressure pattern, but was
more restrictive than cycles 506-508 because even the first submission was
rejected.

## Discovery

The additive `cSum` law closes directly from the cycle-508 closed form:
`push_cast` preserves the named `(q.npow k).cSum` left-hand sides, and
`nlinarith` proves the quadratic identity
`(m+n)(m+n-1) - m(m-1) - n(n-1) = 2mn`.

## Suggested next approach

Keep §38 as the current target. §387 closed-form arithmetic now includes the
additive exponent laws and `n = 3` corollaries. The remaining §387 inverse and
power-homomorphism work is still blocked by the §384 tree-convolution issue,
so the next planning cycle should either commit to a §384 convolution shape or
choose another explicitly unblocked §38 layer.
