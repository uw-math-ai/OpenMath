# Issue: BDF7 zero-instability root certificate

## Blocker
The BDF7 sextic factor still needs a rigorous Lean certificate for a root
outside the closed unit disk. The exact target is:

```lean
∃ ξ : ℂ,
  1089 * ξ ^ 6 - 1851 * ξ ^ 5 + 2559 * ξ ^ 4 -
    2341 * ξ ^ 3 + 1334 * ξ ^ 2 - 430 * ξ + 60 = 0 ∧
  1 < ‖ξ‖
```

Numerically, the unstable conjugate pair is approximately:

```text
ξ = 0.0768046058613277 +/- 1.01932879466066 i
```

## Context
Cycle 377 added the BDF7 definition, consistency/order/implicit proofs,
characteristic factorization, and the reduction:

```lean
private theorem bdf7_not_zeroStable_of_bad_root
    {ξ : ℂ}
    (hQ : 1089 * ξ ^ 6 - 1851 * ξ ^ 5 + 2559 * ξ ^ 4 -
      2341 * ξ ^ 3 + 1334 * ξ ^ 2 - 430 * ξ + 60 = 0)
    (hgt : 1 < ‖ξ‖) :
    ¬ bdf7.IsZeroStable
```

So the remaining mathematical work is only the exact root certificate.

## What was tried
Aristotle batch submitted in cycle 377:

- `572f102d-dd21-487a-8ae9-e610151c1a83`: factorization, `COMPLETE`; rejected as a direct transplant because the output rebuilt a stub `OpenMath/MultistepMethods.lean`.
- `b448e7fa-be3c-4049-b0cf-9866dcd651fc`: bad-root reduction, `COMPLETE`; rejected as a direct transplant because it targeted a simplified stub `IsZeroStable` API. The live proof is already closed locally.
- `8958a948-aed1-43fe-89c8-05f22fbd3927`: root existence, `IN_PROGRESS` at the single post-wait check.
- `6c8b2729-e006-4b88-ba58-1e4a55713e35`: Schur-Cohn/Jury certificate, `IN_PROGRESS` at the single post-wait check.
- `5c49dcda-7819-47dd-bdff-5709a1a070c6`: Rouche/interval certificate, `IN_PROGRESS` at the single post-wait check.

Local Schur recursion for the sextic gives exact coefficient reductions:

```text
[1089, -1851, 2559, -2341, 1334, -430, 60]
-> [8043, -13537, 18413, -16387, 8838, -2430]
-> [19594983, -29133917, 36091783, -29019017, 12729708]
-> [1103657307, -1001989285, 1232276591, -983518033]
-> [4798774195, 2030751691, 7167712264]
```

The last quadratic stage violates the Schur necessary condition because
`7167712264 > 4798774195`.

The Cayley transform `ξ = (1 + w) / (1 - w)` gives:

```text
4 * (2416*w^6 + 3577*w^5 + 4431*w^4 + 3920*w^3
  + 2240*w^2 + 735*w + 105)
```

The Routh-Hurwitz first column includes a negative entry:

```text
2416, 3577, 130183/73, 55036800/130183,
-48719/104, 30164400/48719, 105
```

Equivalently, the fourth Hurwitz determinant is negative:

```text
Δ4 = -1263322645200
```

## Why it failed
The project does not currently have Schur-Cohn/Jury or Routh-Hurwitz
infrastructure connecting these exact arithmetic certificates to the existence
of a polynomial root outside the closed unit disk. The crude triangle-inequality
dominance route is not applicable to these coefficients.

## Possible solutions
1. Formalize the finite Schur-Cohn recursion specialized to real polynomials and
   apply the exact coefficient chain above.
2. Formalize the Cayley-transform plus Routh-Hurwitz necessary condition. The
   negative `Δ4` certificate should imply a transformed root with positive real
   part, hence a BDF7 root with norm greater than one.
3. Build a small Rouche/interval certificate around
   `0.0768046058613277 + 1.01932879466066 i`, with exact rational bounds for
   the disk and a direct norm lower bound.
