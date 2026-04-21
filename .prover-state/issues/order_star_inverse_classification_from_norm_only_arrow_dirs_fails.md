# Issue: Inverse classification from norm-only arrow directions fails

## Blocker
The planned implication

- `IsDownArrowDir R θ` or `IsUpArrowDir R θ`
  `⇒ exp (↑((((p + 1 : ℕ) : ℝ) * θ)) * I) = ±1`

is false for the current live definitions of `IsDownArrowDir` / `IsUpArrowDir`.

Those predicates only record a **norm inequality** along the ray
`t ↦ t * exp (I * θ)`:

- `IsUpArrowDir R θ` means `1 < ‖R(t e^{iθ}) * exp(-(t e^{iθ}))‖` for small `t`
- `IsDownArrowDir R θ` means `‖R(t e^{iθ}) * exp(-(t e^{iθ}))‖ < 1` for small `t`

They do **not** assert that the ray is tangent to the order web, or even that
the leading phase `exp (I * (p + 1) * θ)` is real.

## Context
For the asymptotic model used throughout `OpenMath/OrderStars.lean`,

`R z * exp (-z) = 1 - C * z^(p+1) + O(|z|^(p+2))`,

the leading variation of the norm is controlled by

`‖1 - C * t^(p+1) * exp (I * (p + 1) * θ)‖^2
   = 1 - 2 * C * t^(p+1) * cos ((p + 1) * θ) + higher order terms`.

So from an up/down ray one can at best infer the sign of
`C * cos ((p + 1) * θ)`, not that `cos ((p + 1) * θ) = ±1`, and not that
`exp (I * (p + 1) * θ) = ±1`.

Concrete obstruction:

- In the live file, `forwardEulerR z = 1 + z` has `p = 1` and positive error
  constant `C = 1 / 2`.
- Along `θ = π / 3`, numerical evaluation gives
  `|(1 + t * exp (iπ/3)) * exp (-t * exp (iπ/3))| > 1` for small `t > 0`
  (for example `t = 0.01` gives approximately `1.000024668...`).
- But `exp (I * (p + 1) * θ) = exp (2π I / 3) ≠ ±1`.

So the desired inverse-classification bridge cannot be proved from the current
`IsUpArrowDir` / `IsDownArrowDir` hypotheses alone.

## What was tried
- Added theorem-local skeletons for the generic down/up bridges and for the
  branch-level contradiction theorem.
- Submitted a focused Aristotle batch on:
  - inverse `exp = ±1` classification,
  - generic down/up bridges,
  - down-arrow contradiction.
- Waited 30 minutes and refreshed once.
- The only completed inverse-classification artifact redefined
  `IsUpArrowDir` to include a real-valued/order-web condition, which is exactly
  the missing hypothesis in the live interface and therefore not incorporable.
- Manually checked the analytic shape against the live definition and found the
  obstruction above.

## Possible solutions
- Strengthen the notion of tangent direction used by realized infinity branches:
  require theorem-local/order-web tangency data beyond mere `‖·‖ <> 1`.
- Keep the branch contradiction theorem theorem-local and assume the local cone
  sign control directly, without trying to derive it from the current
  norm-only `IsUpArrowDir` / `IsDownArrowDir`.
- Introduce a new theorem-local hypothesis expressing the missing phase
  condition, e.g. `exp (I * (p + 1) * θ) = ±1`, rather than trying to recover
  it from the present arrow predicates.
