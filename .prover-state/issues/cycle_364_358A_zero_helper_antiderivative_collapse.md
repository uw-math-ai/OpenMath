# Issue: lower-degree antiderivative route collapses before reaching `nodePoly * q`

## Blocker
The current theorem-local scaffold in `OpenMath/CollocationAlgStability.lean`
does not actually reach

```lean
∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x = 0
```

for `q.natDegree < s - 1`.

The obstruction is structural:

1. For the lower-degree case, the antiderivative polynomial
   `Qpoly := antiderivativePoly s q` has degree `< s`.
2. Therefore the quotient by `nodePoly t` should be zero:
   `Qpoly /ₘ nodePoly t = 0`.
3. Hence the remainder is just `Qpoly` itself:
   `Qpoly %ₘ nodePoly t = Qpoly`.

After that collapse, the scaffold only gives the tautological exactness surface

```lean
∑ i, t.b i * q.eval (t.c i) * Qpoly.eval (t.c i)
  = ∫ x in (0 : ℝ)..1, (q * Qpoly).eval x,
```

which implies the algebraic-stability quadratic form is zero, but it no longer
contains any surviving `nodePoly t * q` term. So this route does **not**
produce the desired zero theorem.

## Context
- Live file: `OpenMath/CollocationAlgStability.lean`
- New local scaffold now present:
  - `antiderivativePoly`
  - `antiderivativePoly_eval_node_eq_collocation`
  - `modByMonic_nodePoly_eval_eq`
  - `modByMonic_nodePoly_natDegree_lt`
  - `algStabMatrix_quadForm_eq_antiderivativePoly`
  - `antiderivative_remainder_exact`
- Structured zero-theorem proof now reaches the intermediate claims:
  - quotient-zero surface `Qpoly /ₘ nodePoly t = 0`
  - remainder collapse `r = Qpoly`
  - quadratic-form zero surface `hquad_zero`

The remaining unproved goal is exactly the final `hnode` step.

## What was tried
- Added the theorem-local antiderivative/remainder scaffold and verified:
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/CollocationAlgStability.lean`
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.CollocationAlgStability`
- Submitted the fresh focused Aristotle batch required by the strategy:
  - `c079a3e9-4c78-4766-b961-c9b74333e532` for `antiderivative_remainder_exact`
  - `fb765e3d-98de-4254-afd3-2b928f226032` for `nodePoly_interval_zero_aux_of_algStable`
  - `7b2bf1cb-5eb9-4e45-ad12-8591dd23f0f0` for `stabilityMatrix_quadForm_eq_neg_integral`
  - `409155c2-ac8b-476c-8e1c-f11f8a91cfb5` for `boundary_theta_nonneg_of_algStable`
  - `b3b1362b-0567-4a48-b42d-d65635586332` for `orthogonal_degree_eq_boundaryPoly`
- Per the single allowed refresh, none completed:
  - `c079a3e9-...`: `IN_PROGRESS` at 6%
  - `fb765e3d-...`: `IN_PROGRESS` at 4%
  - `7b2bf1cb-...`: `QUEUED`
  - `409155c2-...`: `IN_PROGRESS` at 4%
  - `b3b1362b-...`: `QUEUED`

## Possible solutions
- Re-target the antiderivative step to a polynomial whose division by
  `nodePoly t` leaves a **nonzero** quotient even in the lower-degree case,
  so the desired `∫ nodePoly * q` term survives.
- Abandon the antiderivative-of-`q` route for the zero theorem and derive the
  lower-degree vanishing by polarization from a degree-`s - 1` sign statement,
  if that dependency reversal is mathematically unavoidable.
- Return to the transformed polynomial basis from the textbook proof and prove
  the lower-degree zero identity directly, instead of forcing it through the
  current remainder decomposition.
