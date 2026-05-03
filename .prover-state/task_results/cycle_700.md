# Cycle 700 Results

## Worked on
§521 Step C.15 — BDF consistency check for the cycle 698 general LMM
textbook headline. Stretch Step C.16 — scalar evaluation corollary at
arbitrary complex `ξ`.

Active file: `OpenMath/LMMAsGLM/StabilityCharpoly.lean`.

## Approach
Followed the strategy verbatim:

1. Located the cycle 698 headline at line 1543
   (`D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_plus_residual`)
   and the cycle 643 BDF headline at line 464
   (`D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_of_bdf`).
2. Appended `residual_eq_X_pow_mul_correction_of_bdf` after line 1565
   exactly as the strategy specified.
3. First attempt: `linear_combination hbd - hgen`.
4. After C.15 landed, appended the stretch
   `D_mul_toGLM_charpoly_eval_eq` (Step C.16) using
   `congrArg (Polynomial.eval ξ)` plus `simpa` over the standard
   `Polynomial.eval_*` lemmas, exactly as written in strategy.md.

## Result
SUCCESS for both C.15 and C.16.

- Step C.15 closed by `linear_combination hgen - hbd` (sign flipped
  from initial guess; see "Dead ends" below).
- Step C.16 closed by `simpa [Polynomial.eval_mul, …]` over
  `congrArg (Polynomial.eval ξ) h` on first attempt, no adjustment
  needed.

`lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean` returns 0
errors / 0 warnings in ~9 s (incremental).

File grew from 1567 → 1627 lines (cap 3000, well clear).

## Dead ends
The strategy's first-suggested sign `linear_combination hbd - hgen`
left a goal of the shape

```
m.rowYQuot * X^s * C(z·β_last) · 2
  − (X^s · C(z) · ∑ …) · 2
  + m.rowFAlphaPoly · C(z) · 2
  + (PY(0).charpoly · m.rowFBetaPoly) · C(z) · 2
  = 0
```

i.e. the residual was doubled relative to the correction sum. That is
exactly the "if the sign is wrong, try `linear_combination hgen - hbd`"
fallback the strategy anticipated. Flipping the sign closed the goal
without further intervention. (Linear-combination convention here:
`linear_combination e` reduces `lhs = rhs` to `(lhs − rhs) − (e_lhs −
e_rhs) = 0`; with `e = hbd − hgen` the residual gets added rather than
cancelled, hence the doubling.)

No `ring_nf` rewrite or manual algebra fallback was needed.

## Discovery
The cycle 698 headline + cycle 643 BDF headline are now linked by the
explicit polynomial identity

```
residual = X^s · C(z) · correction       (under BDF)
```

which fingerprints internal consistency between the active-form and
textbook-form residuals. This bridge is reusable for any future cycle
that needs to translate between active-form residuals and the textbook
correction term — in particular for step counts on the way to
`LMM.toGLM_isAStable_iff`.

The Step C.16 evaluation corollary is the cleanest scalar form of the
cycle 698 headline. Future root-counting / `IsAStable` work can use
`D_mul_toGLM_charpoly_eval_eq` directly without re-deriving the
distribution of `Polynomial.eval ξ` across the headline.

## Suggested next approach
The cycle 698–700 chain has now landed:

- Cycle 698: general polynomial headline (C.14).
- Cycle 700 Step C.15: BDF consistency bridge.
- Cycle 700 Step C.16: scalar evaluation corollary.

Reasonable next planner targets, in order of "how much creative work
needed":

1. **Roots of `m.toGLM.stabilityMatrix z .charpoly` ↔ roots of
   `m.stabilityPolyPoly z`** (under `hz ≠ 0` and `hs > 0`):
   factor the C.16 identity. The `X^s · …` term has root structure
   tightly controlled by the residual; with hz·β_last ≠ 0 the
   identity gives a near-explicit dictionary between non-zero roots
   of the matrix charpoly and roots of the textbook polynomial.
2. **A-stability scalar form**: build
   `LMM.toGLM_isAStable_iff_stabilityPolyPoly_…` (textbook §521,
   eqn. (521b) onwards) by feeding C.16 into the scalar `IsAStable`
   condition. This is the long-term §521 target the plan flagged but
   that the strategy explicitly forbade attempting in cycle 700.
3. **Coefficient extraction**: write
   `(m.toGLM.stabilityMatrix z .charpoly).coeff k` in terms of
   `(m.stabilityPolyPoly z).coeff (k − s)` plus a residual coefficient.
   Useful for explicit characteristic-polynomial computations in
   small-`s` examples (BDF1, BDF2, BDF3, …).

All three are single-headline targets compatible with the
"narrow concrete identity per cycle" pattern that has been working
since cycle 696.
