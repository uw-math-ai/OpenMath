# Issue: `stabilityMatrix_quadForm_eq_neg_integral` is blocked on the top-degree defect identity

## Blocker
In `OpenMath/CollocationAlgStability.lean`, the upstream B-upgrade route is now live:

- `monomialVec_D_of_algStable` is proved,
- `satisfiesB_two_mul_sub_one_of_algStable` now closes the `B(2 * s - 1)` upgrade,
- `nodePoly_interval_zero_aux_of_algStable` compiles from that route.

The next live blocker is the theorem
`stabilityMatrix_quadForm_eq_neg_integral`. The proof now needs a direct
matrix-to-integral identity for degree-`≤ s - 1` test polynomials without
reopening the rejected antiderivative / `%ₘ nodePoly` / quotient-remainder route.

## Context
- Live file: `OpenMath/CollocationAlgStability.lean`
- Current target:

```lean
lemma stabilityMatrix_quadForm_eq_neg_integral
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable)
    (q : ℝ[X]) (hq : q.natDegree ≤ s - 1)
    (hzero : ∀ r : ℝ[X], r.natDegree < s - 1 →
      ∫ x in (0 : ℝ)..1, ((nodePoly t) * r).eval x = 0) :
    let v : Fin s → ℝ := fun i => q.eval (t.c i)
    ∑ i : Fin s, ∑ j : Fin s, v i * t.algStabMatrix i j * v j =
      -2 * (q.leadingCoeff / (s : ℝ)) *
        ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x
```

## What was tried
- Closed the preceding seam by adding the theorem-local helper
  `algStabMatrix_monomial_row_action` and proving
  `monomialVec_D_of_algStable`.
- Rechecked the file with:
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/CollocationAlgStability.lean`
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.CollocationAlgStability`
- Sketched the next proof around the correct defect mechanism:
  - lower-degree pieces should vanish by `B(2 * s - 1)` exactness,
  - the only surviving contribution should come from the top `X^(s - 1)` term,
  - the right-hand side should be recovered from the degree-`2 * s - 1`
    defect of `nodePoly t * X^(s - 1)`.

## Possible solutions
- Prove a monomial bilinear helper first:

```lean
∑ i, ∑ j, t.c i ^ m * t.algStabMatrix i j * t.c j ^ n = 0
```

whenever `m, n < s` and `m + n ≤ 2 * s - 3`.

- Then split `q` into its top term plus lower-degree remainder:

```lean
q = Polynomial.C q.leadingCoeff * Polynomial.X ^ (s - 1) + r
```

with `r.natDegree < s - 1`, and show:
  - the remainder-remainder and top-remainder quadratic-form pieces vanish,
  - `hzero` kills the lower-degree integral contribution,
  - the top-top quadratic form matches the degree-`2 * s - 1` defect of
    `nodePoly t * X^(s - 1)`.

- Keep the proof entirely in the live file; do not reintroduce any auxiliary
  antiderivative or quotient-by-`nodePoly` infrastructure.
