# Issue: Legendre Gaussian bridge still lacks a reusable mapped shifted-Legendre connection

## Blocker
`OpenMath/Legendre.lean` still has two `sorry`s:
- `ButcherTableau.gaussLegendre_B_double`
- `ButcherTableau.gaussLegendreNodes_of_B_double`

The easy high-range decomposition is already in place, and the Euclidean-division helper from
`OpenMath/ShiftedLegendreDivision.lean` compiles. The remaining gap is the actual bridge from the
recursive `shiftedLegendreP` node condition to Mathlib's mapped `Polynomial.shiftedLegendre`, plus
an orthogonality argument that compiles in the current OpenMath environment.

## Context
- `OpenMath/Legendre.lean` currently proves:
  - `gaussLegendre_high_range`
  - `shiftedLegendre_coeff_self_ne_zero`
  - `gaussLegendreNodes_eval_map_shiftedLegendre_zero` assuming a bridge hypothesis
- `OpenMath/ShiftedLegendreDivision.lean` proves `monomial_div_mod_shiftedLegendre`
- Aristotle result `d6ea37d4-7729-48b1-be0d-f5f753e18f63` was already fully incorporated in spirit:
  it only supplied the `k = s + (j + 1)` range witness now present as `gaussLegendre_high_range`
- Aristotle result `ea375b78-11b6-4ed8-9526-ee3e7beff5df` contains a promising orthogonality proof,
  but it does not compile cleanly against the current project/Mathlib API without repair

## What was tried
- Reproduced the reported CI failure and checked the exact GitHub Actions log for run `24641918796`
- Verified the CI failure was historical: it came from `lean-action` failing during `lake exe cache get`
  on commit `ff5b2b124b325b4eef636d308baf1885a2d147df`, while current `main` already contains the
  workflow fix (`8aea4bc23c`, `d27e9bc433`) and builds locally
- Read the two planner-provided Aristotle result directories
- Attempted to import the orthogonality theorem from the Aristotle artifact into a dedicated helper
  module; the proof failed in the induction step around `Polynomial.derivative_comp` and endpoint
  vanishing, so the partial integration was reverted to keep the tree green

## Possible solutions
- Prove a standalone theorem in the main codebase:
  `shiftedLegendreP s x = (-1 : ℝ)^s * (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).eval x`
  This would let `gaussLegendreNodes_eval_map_shiftedLegendre_zero` discharge the node-vanishing side cleanly.
- Repair and integrate the Aristotle orthogonality proof in a separate helper file before touching
  `gaussLegendre_B_double`.
- Alternatively, port the older `quadrature_exactness_step` development from prior Aristotle artifacts
  into a clean helper module, then use it to finish the high-degree branch of `gaussLegendre_B_double`.
