# Cycle 387 Results

## Worked on
Adams–Bashforth 6-step (AB6) in `OpenMath/AdamsMethods.lean`, plus the
Dahlquist convergence wrapper in `OpenMath/DahlquistEquivalence.lean`.

## Approach
Followed the cycle strategy's mechanical AB5 transplant.

Before editing, cross-checked the AB6 β coefficients by exact rational
Lagrange interpolation on the six Adams-Bashforth nodes `[-5,-4,-3,-2,-1,0]`
and integration over `[0,1]` in a Lean scratch run. The run returned:

```text
[-95 / 288, 959 / 480, -3649 / 720, 4991 / 720, -2641 / 480, 4277 / 1440]
1
```

This is exactly
`[-475/1440, 2877/1440, -7298/1440, 9982/1440, -7923/1440, 4277/1440]`,
with coefficient sum `1`. Also checked the numerator sum by `norm_num`.

Added the sorry-first AB6 structure, verified `OpenMath/AdamsMethods.lean`
compiled with the expected sorry warnings, then closed all sorries locally.
No Aristotle jobs were submitted, per the cycle-specific mechanical-task
exception.

## Result
SUCCESS.

Implemented and proved:
- `adamsBashforth6 : LMM 6`
- `adamsBashforth6_consistent`
- `adamsBashforth6_explicit`
- `adamsBashforth6_order_six`
- `adamsBashforth6_zeroStable`
- `adamsBashforth6_convergent`

Updated `plan.md` to mark AB6 complete and set AM6 as the next current target.

Verification:
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/AdamsMethods.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/DahlquistEquivalence.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build`

## Dead ends
None. The only transient issue was that `DahlquistEquivalence.lean` initially
imported the stale compiled `OpenMath.AdamsMethods` artifact before the Adams
module was rebuilt; `lake build OpenMath.AdamsMethods` refreshed it.

## Discovery
The AB6 coefficients in oldest-first order match the denominator-1440 standard:
`[-475, 2877, -7298, 9982, -7923, 4277] / 1440`.

The AB5 zero-stability proof transplants directly with the expected exponent
bump from `ξ ^ 4 * (ξ - 1)` to `ξ ^ 5 * (ξ - 1)`.

## Suggested next approach
Formalize AM6 next in `OpenMath/AdamsMethods.lean`: implicit 6-step, order 7,
denominator 60480, with nonzero last β coefficient, then add the corresponding
Dahlquist convergence wrapper.
