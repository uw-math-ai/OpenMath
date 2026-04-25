# Cycle 388 Results

## Worked on
Adams–Moulton 6-step (AM6) — definition, consistency, implicit, order 7,
zero-stability (in `OpenMath/AdamsMethods.lean`) and convergence wrapper
(in `OpenMath/DahlquistEquivalence.lean`).

## Approach
Followed the strategy's AM5-transplant pattern. Before writing any Lean,
verified the β coefficients via exact rational Lagrange interpolation in
Python over nodes `[-5,-4,-3,-2,-1,0,1]`, integrating the basis polynomials
over `[0,1]`.

## Result
SUCCESS. All AM6 theorems closed on first compile. Full `lake build`
succeeds with no errors. No `sorry`s remain.

- `adamsMoulton6 : LMM 6` defined.
- `adamsMoulton6_consistent`
- `adamsMoulton6_implicit` (β₆ = 19087/60480 ≠ 0)
- `adamsMoulton6_order_seven`
- `adamsMoulton6_zeroStable` (ξ⁵(ξ-1), simple root at 1)
- `adamsMoulton6_convergent` (via `dahlquist_equivalence`)

## Important correction (strategy had wrong coefficients)
The cycle-388 strategy listed β as
`[863, -6737, 25527, -56121, 76427, -65112, 19087] / 60480`. This is
**incorrect** — the digits/signs do not match the standard AM6 table and
the sum is not 1.

The correct coefficients (oldest-first, denominator 60480), verified by
rational Lagrange interpolation and matching Hairer–Norsett–Wanner Vol I
table III.1.2, are:

```
[-863, 6312, -20211, 37504, -46461, 65112, 19087] / 60480
```

These sum to exactly 1 (consistency: σ(1) = ρ'(1) = 1). I used the
correct values.

## Stale Aristotle bundles (per strategy P0)
Confirmed the two listed Aristotle bundles target BDF7 (already closed in
cycle 379). Did not incorporate, did not open issue files. They can be
discarded.

## Aristotle batch
Skipped per the strategy's allowance: AM6 closed cleanly on first compile
via the AM5 transplant pattern, so an Aristotle batch would be redundant
make-work. Strategy explicitly permitted skipping if all proofs land
manually.

## Dead ends
None. The AM5 template was a perfect fit; the only friction was that the
strategy's β table was wrong, which I caught during the up-front
verification step (this is exactly why the strategy mandated that step).

## Discovery
- The mechanical Adams family (AB2–AB6, AM2–AM6) is now complete in the
  formalization tree.
- Up-front coefficient verification via Python rational arithmetic caught
  a strategy error before any Lean was written. Future mechanical-table
  cycles should keep this gate.

## Suggested next approach
- The mechanical Adams extension milestone is exhausted. Pivot back to
  deep theorems:
  1. Theorem 359D — needs Iserles §3.5.10 lookup to identify the named
     theorem after 359C. The §3.5.10 packaging corollaries from cycle 376
     give a clean BN-stability scaffold to plug the real 359D statement
     into.
  2. If the §3.5.10 reference is not yet in hand, start Chapter 4 BDF
     downstream (predictor-corrector pairs, Nordsieck representation, or
     §1.3 order/convergence structure beyond Theorem 213A).
- Do **not** attempt AM7/AB7 — the planner explicitly cut the mechanical
  Adams extension at AM6 to pivot back to deep theorems.
