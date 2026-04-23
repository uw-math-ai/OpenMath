# Issue: theorem-local `D(k+1)` extraction is stuck on row-action normalization

## Blocker
In `OpenMath/CollocationAlgStability.lean`, the new B-upgrade route now proves:

- the monomial quadratic-form identity,
- vanishing of that quadratic form under a high-enough `B` condition,
- the generic PSD-to-kernel lemma
  `algStabMatrix_mulVec_zero_of_psd_of_quadForm_zero`.

The remaining blocker is turning the resulting row-action statement

```lean
∑ i : Fin s, t.algStabMatrix j i * t.c i ^ k = 0
```

into the explicit theorem-local `D(k+1)` identity

```lean
∑ i : Fin s, t.b i * t.c i ^ k * t.A i j
  = t.b j / (((k + 1 : ℕ) : ℝ)) * (1 - t.c j ^ (k + 1)).
```

This is exactly the open lemma `monomialVec_D_of_algStable`.

## Context
- Live file: `OpenMath/CollocationAlgStability.lean`
- Current proved seam:
  - `algStabMatrix_monomial_quadForm_zero`
  - `algStabMatrix_mulVec_zero_of_psd_of_quadForm_zero`
  - `moment_upgrade_from_D`
  - rewritten `nodePoly_interval_zero_aux_of_algStable`
- Current remaining dependency chain:
  - `monomialVec_D_of_algStable`
  - `satisfiesB_two_mul_sub_one_of_algStable`
  - later `stabilityMatrix_quadForm_eq_neg_integral`

## What was tried
- Manual normalization attempts from
  `∑ i, t.algStabMatrix j i * t.c i ^ k = 0`
  by:
  - expanding `algStabMatrix`,
  - separating the three sums,
  - rewriting the `A j i` term with `C(k+1)`,
  - rewriting the `b i` moment with `B(k+1)`,
  - then solving the scalar equation with `field_simp` / `nlinarith`.
- These attempts all hit the same Lean friction point:
  finite-sum normalization does not line up definitionally, so rewrites like
  `rw [hCsmall, hBsmall]` do not fire on the expanded row-action expression
  without extra theorem-local reshaping.
- Fresh Aristotle batch:
  - `ffda8780-21da-427d-8ea0-3d168ade76b3` (`monomialVec_D_of_algStable`) came
    back `COMPLETE_WITH_ERRORS` with the right proof idea, but its `convert` /
    `simp_all` normalization does not transplant directly to the live file.
  - `9c1a6e55-7847-4b67-9d36-b68bce89bd85` (`moment_upgrade_from_D`) came back
    `COMPLETE_WITH_ERRORS` and its proof body *was* salvageable; that helper is
    now live.

## Possible solutions
- Prove a tiny local reshaping lemma that turns

  ```lean
  ∑ i, t.algStabMatrix j i * t.c i ^ k
  ```

  into the separated form

  ```lean
  t.b j * (∑ i, t.A j i * t.c i ^ k)
    + (∑ i, t.b i * t.c i ^ k * t.A i j)
    - t.b j * (∑ i, t.b i * t.c i ^ k).
  ```

  Once that exact normal form is available, `C(k+1)` and `B(k+1)` should rewrite
  cleanly.
- Alternatively, avoid rewriting under the raw expanded sum and first prove
  helper lemmas for

  ```lean
  ∑ i, t.b j * t.A j i * t.c i ^ k
  ```

  and

  ```lean
  ∑ i, t.b j * t.b i * t.c i ^ k
  ```

  so the row-action equality can be rewritten in two or three controlled steps
  instead of one large `simp_all`.
