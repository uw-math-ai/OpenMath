# Issue: GLM A-stability transports for `rkRadauIIA3` and `rkGaussLegendre3`

## Blocker

Cycle 652 landed `rkSDIRK2_toGLM_isAStable` and `rkSDIRK3_toGLM_isAStable`
in `OpenMath/RKAsGLM.lean` using a generic recipe:

1. State `(1 - z • Aℂ) = !![..]` for an explicit lower-triangular matrix.
2. Compute `det = (1 - z·λ)^s` (very clean for SDIRK because A is
   lower triangular with constant diagonal).
3. `Matrix.inv_def` + `Matrix.adjugate_fin_two_of` /
   `Matrix.adjugate_fin_three_of` + `Ring.inverse_eq_inv'`.
4. `simp only [...]; push_cast; field_simp; ring` to reduce to
   `sdirkNStabilityFn = sdirkNNum / sdirkNDenom`.

This recipe does **not** transfer to `rkRadauIIA3` or
`rkGaussLegendre3`. Both tableaux have:

- `Real.sqrt 6` in `rkRadauIIA3.A` (entries like
  `(296 - 169 * Real.sqrt 6) / 1800`).
- `Real.sqrt 15` in `rkGaussLegendre3.A` (entries like
  `2/9 - Real.sqrt 15 / 15`).

The matrices are **not** triangular: every off-diagonal entry is
non-zero, so the `Matrix.det_fin_three` expansion produces six terms
each of which carries a `Real.sqrt 6` (or `Real.sqrt 15`) factor.
The resulting determinant identity

```
det (1 - z • A) = radauIIA3Denom z      -- = 1 - 3z/5 + 3z²/20 - z³/60
det (1 - z • A) = gl3Q z / 120          -- = (120 - 60z + 12z² - z³) / 120
```

is true (this is a classical fact: stiffly accurate symmetric
collocation methods produce diagonal Padé denominators with rational
coefficients, with all `√6` / `√15` cross terms cancelling), but
proving it in Lean requires algebraic manipulation modulo
`Real.sqrt 6 ^ 2 = 6` (or `Real.sqrt 15 ^ 2 = 15`).

A straight `simp [Matrix.det_fin_three]; ring` does not close the
identity because `Real.sqrt 6` is not a polynomial atom — `ring`
treats it as an opaque variable, so any cancellation that depends on
`(Real.sqrt 6)^2 = 6` is invisible to `ring`.

`linear_combination` with the appropriate `sqrt6_sq` certificate
should close it, but the certificate polynomial is **non-trivial**.
For example, the determinant expansion at degree 3 in z mixes
`Real.sqrt 6` linearly through 6 cross terms; the certificate must
encode every cross-term cancellation. Hand-deriving this polynomial
is tractable but error-prone.

A short attempt during cycle 652 hit a `simp` stack overflow when
trying to unfold `Matrix.one_apply` together with `Fin (3)` decidable
equality on `rkRadauIIA3` — the search blew through the heartbeat
budget before producing a tractable goal. That suggests the bridge
needs a more controlled rewrite chain than `simp only [..., rkRadauIIA3,
Matrix.one_apply, ...]`.

## Context

Existing classical scalar A-stability:
- `OpenMath/RadauIIA3.lean:229` — `radauIIA3_aStable z hz : ‖radauIIA3StabilityFn z‖ ≤ 1`
- `OpenMath/GaussLegendre3.lean:198` — `gl3_aStable z hz : ‖gl3StabilityFn z‖ ≤ 1`

GLM iff bridge consumed:
- `OpenMath/RKAsGLM.lean:94` — `ButcherTableau.toGLM_isAStable_iff`

What needs to land:

```lean
theorem rkRadauIIA3_stabilityFunction_eq (z : ℂ) (hz : z.re ≤ 0) :
    rkRadauIIA3.stabilityFunction z = radauIIA3StabilityFn z := ...

theorem rkGaussLegendre3_stabilityFunction_eq (z : ℂ) (hz : z.re ≤ 0) :
    rkGaussLegendre3.stabilityFunction z = gl3StabilityFn z := ...
```

After which the GLM transports are one-line:

```lean
theorem rkRadauIIA3_toGLM_isAStable : rkRadauIIA3.toGLM.IsAStable := by
  rw [ButcherTableau.toGLM_isAStable_iff]
  intro z hz
  rw [rkRadauIIA3_stabilityFunction_eq z hz]
  exact radauIIA3_aStable z hz
```

## What was tried

- `Matrix.det_fin_three` followed by `simp only [..., Matrix.one_apply,
  rkRadauIIA3, ...]` to unfold the determinant. The `simp` call looped
  / stack-overflowed when `if h : (i = j) then 1 else 0` from
  `Matrix.one_apply` was combined with `Fin 3` decidable equality and
  the heavy `rkRadauIIA3` unfold.
- A manual `if_false` injection via `show ((0 : Fin 3) = (1 : Fin 3))
  ↔ False from by decide` followed by `simp only [..., if_false]`
  pre-simplified the diagonal pattern but still failed to close the
  determinant identity in a `ring` step because of `Real.sqrt 6`.

## Possible solutions

1. **Linear-combination certificate.** Prove the determinant identity
   via `linear_combination C * sqrt6_sq` where `C` is the cross-term
   cancellation polynomial. This requires hand-deriving `C`. The
   degree of `C` should be ≤ 4 in `(z, sqrt6)` based on the structure
   of the determinant.
2. **Structured matrix decomposition.** Decompose `A = A₀ + sqrt6·A₁`
   into rational and irrational parts. Then `det(1 - zA) = det(1 -
   zA₀ - z·sqrt6·A₁)`, which can be expanded as a polynomial in
   `sqrt6` whose `(sqrt6)²` terms collapse via `sqrt6² = 6`. This may
   give a cleaner proof structure than a single `linear_combination`.
3. **Direct evaluation via Padé identity.** Use the fact that
   collocation methods produce stability functions equal to the
   diagonal Padé approximant (Iserles Theorem 4.6 / Hairer–Wanner
   Theorem IV.5.4). If a generic `collocation_stabilityFunction` 
   identity is available in `OpenMath/Collocation.lean`, the bridge
   becomes a corollary. Worth checking — `OpenMath/Pade.lean` already
   has Padé apparatus.

## Suggested next cycle

Approach 3 is most leverage-y: a one-time investment in a
collocation → Padé bridge gives both Radau IIA and GL3 (and any
future collocation-based RK method) for free.

Approach 1 is the least invasive but needs careful certificate
derivation. Estimate: 1 cycle if the certificate is straightforward,
2-3 if it has subtle sign/coefficient issues.

Cycle 652 explicitly skipped these per the strategy guidance "do not
fight the alignment", and committed `rkSDIRK2_toGLM_isAStable` and
`rkSDIRK3_toGLM_isAStable` instead. That covers two of the four
strategy targets.
