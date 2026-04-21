# Issue: Padé order-star bridge still lacks a nonzero coincidence exclusion

## Blocker
`OpenMath/PadeOrderStars.lean` now states the first concrete Padé-side order-star
consumer and the first concrete analytic theorem boundary:

- `thm_355D_of_padeR`
- `thm_355E'_of_padeR`
- `padeR_no_nonzero_eq_exp_on_orderWeb`

The wrappers compile, but the concrete theorem

`∀ z : ℂ, z ≠ 0 → z ∈ orderWeb (padeR n d) → padeR n d z = exp z → False`

is still only in sorry-first form. This is now the first live missing analytic
statement on the Padé side.

## Context
- New live file: `OpenMath/PadeOrderStars.lean`
- The abstract seam in `OpenMath/OrderStars.lean` already exposes:
  - `ConcreteRationalApproxToExp`
  - `thm_355D_of_concreteRationalApprox`
  - `thm_355E'_of_concreteRationalApprox`
- `OpenMath/Pade.lean` defines the concrete family `padeR` and proves:
  - Padé numerator/denominator recurrences
  - approximation-order bookkeeping
  - diagonal symmetry / self-adjointness facts
  - low-degree A-stability facts
- But there is still no live theorem controlling nonzero solutions of
  `padeR n d z = exp z` on `orderWeb (padeR n d)`.
- The next concrete branch-level inputs are also unstated in live code:
  zero-support exclusion for realized branches, local cone sign control, and
  far-field sign control for `padeR`.

## What was tried
- Added `OpenMath/PadeOrderStars.lean` so the concrete `R := padeR n d` target
  exists in live code instead of only inside `OpenMath/OrderStars.lean`.
- Verified that the concrete wrapper theorems compile.
- Left `padeR_no_nonzero_eq_exp_on_orderWeb` in sorry-first form.
- Submitted a focused Aristotle batch on:
  - `padeR_no_nonzero_eq_exp_on_orderWeb`
  - down/up zero-support exclusion for realized Padé branches
  - local cone-sign package for `padeR`
  - far-field sign package for `padeR`
- Re-checked `OpenMath/Pade.lean` for any existing theorem that already excludes
  nonzero coincidence points of `padeR` with `exp`; none was found.

## Possible solutions
- Prove a Padé-specific global theorem excluding nonzero zeros of
  `fun z => exp z - padeR n d z` on the positive-real order web.
- If the uniform `(n,d)` theorem is too strong, restrict first to the concrete
  Padé subfamily actually needed next and make those hypotheses theorem-local.
- Derive the exclusion from stronger analytic input already suggested by the
  seam: zero not in realized branch support, local sign control near the origin,
  and far-field sign control on large order-web points.
- Import additional Padé-side structure only if it stays concrete and does not
  reintroduce a generic arbitrary-`R` theorem that is already known to be false.
