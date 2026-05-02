# Cycle 631 Results

## Worked on

§521 LMM A-stability — second concrete LMM-side transport through the
§503 GLM embedding: `trapezoidalRule_toGLM_isAStable` in
`OpenMath/LMMAsGLM.lean`.

## Approach

Followed the cycle 630 direct `s = 1` recipe rather than attempting any
general `LMM.toGLM_isAStable_iff` bridge. Aristotle was intentionally
skipped per the cycle strategy.

The actual trapezoidal stability matrix is not triangular:

```lean
!![2 / (2 - z), 1 / (2 - z);
  2 * z / (2 - z), z / (2 - z)]
```

It is rank one. Its trace is `(2 + z) / (2 - z)` and its determinant is
`0`, so `Matrix.charpoly_fin_two` gives the desired factorisation
`X * (X - C ((2 + z) / (2 - z)))`. The root split is therefore still
`μ = 0` or `μ = (2 + z)/(2 - z)`.

For the nonzero root, reused the existing trapezoidal analytic core:
from `z.re ≤ 0`, prove `‖2 + z‖^2 ≤ ‖2 - z‖^2`, then
`‖2 + z‖ ≤ ‖2 - z‖`, and finish with `norm_div` and `div_le_one`.

## Result

SUCCESS. `trapezoidalRule_toGLM_isAStable :
trapezoidalRule.toGLM.IsAStable` lands sorry-free in
`OpenMath/LMMAsGLM.lean`.

`lake env lean OpenMath/LMMAsGLM.lean` passes cleanly. `plan.md` was
updated to record the cycle 631 milestone and to suggest `bdf2` as the
next plausible concrete LMM-side §521 target.

## Dead ends

- The planner's optimistic shape with `[0,0] = (2+z)/(2-z)` and a
  triangular charpoly split was not the actual §503 embedding shape.
  The `[0,1]` entry is nonzero, but the full matrix is rank one, so the
  determinant-zero route avoids the harder quadratic eigenvalue analysis.
- Direct `Matrix.charpoly` / `Matrix.det_fin_two` expansion produced
  awkward polynomial algebra. Switching to `Matrix.charpoly_fin_two`
  plus separate trace and determinant computations was much cleaner.

## Discovery

For one-step LMMs with the §503 state vector `(y_n, h f_n)`, the
trapezoidal GLM stability matrix carries the amplification factor as its
trace, not as the `[0,0]` entry. This is still consistent with the
expected extra zero eigenvalue from the enlarged GLM state.

## Suggested next approach

Next §521 cycle can either attempt another concrete transport such as
`bdf2_toGLM_isAStable` at `s = 2`, or first add a reusable helper for
rank-one / determinant-zero concrete stability matrices. The general
`LMM.toGLM_isAStable_iff` bridge remains open and should still wait for
the structural general-`s` charpoly factorisation.
