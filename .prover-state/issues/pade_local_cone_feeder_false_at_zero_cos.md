# Issue: Padé local cone feeder route fails at zero-cosine rays

## Blocker
The cycle-311 target

```lean
IsDownArrowDir (padeR n d) θ ->
  ∃ aperture > 0, ∃ radius > 0,
    ∀ z ∈ rayConeNearOrigin θ aperture radius,
      ‖padeR n d z * exp (-z)‖ < 1
```

and its up-arrow analogue appear to be false as stated.

The obstruction is the zero-cosine case

```lean
Real.cos ((↑(n + d) + 1) * θ) = 0.
```

Along such an exact ray, the order-star amplitude can still stay on one side of
`1`, but any open cone around the ray can immediately contain nearby angles with
the opposite sign.

## Context
Concrete numerical evidence on the live Padé example `padeR 1 0 = forwardEulerR`
at `θ = π / 4`:

- exact ray, `t = 10^-3`:
  `|(1 + t e^{iπ/4}) e^{-t e^{iπ/4}}| - 1 ≈ -2.35e-10`
- nearby angle, `θ = π / 4 + 0.01`, same `t = 10^-3`:
  `|(1 + t e^{i(π/4+0.01)}) e^{-t e^{i(π/4+0.01)}}| - 1 ≈ +9.76e-09`

So the exact ray is locally on the `< 1` side, but every cone around it picks
up nearby points on the `> 1` side. This kills the proposed feeder statement
from `IsDownArrowDir` to a uniform cone neighborhood.

The same phenomenon also blocks the proposed sign-extraction lemmas

```lean
IsDownArrowDir (padeR n d) θ ->
  0 < padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ)

IsUpArrowDir (padeR n d) θ ->
  padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) < 0
```

because an exact-ray arrow can occur at a zero-cosine angle.

## What was tried
- Added sorry-first skeletons for the cycle-311 cone/sign theorems in
  `OpenMath/OrderStars.lean` and `OpenMath/PadeOrderStars.lean`.
- Proved the quantitative helper lemmas
  `main_minus_bound_of_re_pos` and `main_plus_bound_of_re_neg`.
- Tried to prove the honest cosine-sign cone lemmas by a unified
  `coeff := |C|`, `base := if 0 ≤ C then η else -η` argument.
- The public theorem proof became large enough to hit the 200000-heartbeat cap.
- Checked the forward-Euler / `padeR 1 0` zero-cosine ray numerically; that
  exposed the deeper problem that the planned `IsDownArrowDir/IsUpArrowDir`
  feeder statements themselves are not valid at zero-cosine rays.

## Possible solutions
- Weaken the feeder hypothesis from `IsDownArrowDir` / `IsUpArrowDir` to an
  explicit cosine-sign assumption:

  ```lean
  0 < padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ)
  ```

  and the matching negative-sign version for the up case.
- Alternatively, replace the target by a one-sided wedge statement that excludes
  zero-cosine rays, rather than a symmetric cone around an arbitrary arrow ray.
- Keep the proved quantitative helper lemmas and finish only the honest
  cosine-sign cone infrastructure first; do not try to derive it from
  `IsDownArrowDir` / `IsUpArrowDir` without an extra nonzero cosine margin.
