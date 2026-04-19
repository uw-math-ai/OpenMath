# Issue: Legendre bridge and orthogonality blocker

## Blocker
`ButcherTableau.gaussLegendre_B_double` is reduced to the high-degree case `k = s + (j + 1)` with `j < s`, but the proof still needs a clean way to pass from the recursive `shiftedLegendreP` to explicit polynomial coefficients and then show the orthogonality identity

`∑ l, a l / ((l : ℝ) + (j : ℝ) + 1) = 0`.

## Context
- File: `OpenMath/Legendre.lean`
- Current local progress inside `gaussLegendre_B_double`:
  - proved
    `(Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre s)).coeff s ≠ 0`
  - remaining `sorry` is still the hard Gaussian quadrature step
- Mathlib resource:
  - `Polynomial.shiftedLegendre`
  - `Polynomial.coeff_shiftedLegendre`
  - `Polynomial.factorial_mul_shiftedLegendre_eq`

## What was tried
- Checked all mandated Aristotle jobs and extracted the completed outputs.
- Attempted an inline bridge theorem
  `shiftedLegendreP n x = (-1 : ℝ)^n * eval x (map (Int.castRingHom ℝ) (shiftedLegendre n))`.
- The direct coefficient-recurrence proof became fragile in the `n + 2` step:
  the polynomial recurrence itself is plausible, but converting it into a clean evaluation identity produced messy coefficient sums and parity rewrites.

## Possible solutions
- Clean up the bridge proof from Aristotle job `1d9822aa-9d1d-4d23-abf6-501995a5f6a8`, but keep it as a local `have` inside `gaussLegendre_B_double`.
- Avoid the full bridge and instead prove orthogonality algebraically from Rodrigues:
  define a coefficient functional `F(p) = ∑ coeff p l / (l + j + 1)` and perform repeated polynomial integration-by-parts without `intervalIntegral`.
- If Aristotle returns a usable bridge or orthogonality proof from:
  - `0d264cc7-de25-41eb-a979-b61742eefbe2`
  - `9fbcf32d-ad21-480d-8332-3593305f5abc`
  incorporate that directly next cycle.
