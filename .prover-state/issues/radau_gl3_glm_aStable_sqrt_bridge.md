# Issue: GLM A-stability transport for `rkGaussLegendre3`

## Status

Cycle 653 resolved the Radau IIA half of this issue:

- `rkRadauIIA3_stabilityFunction_eq`
- `rkRadauIIA3_toGLM_isAStable`

The landed proof in `OpenMath/RKAsGLM.lean` uses a split certificate:
`det M = radauIIA3Denom z`, an explicit `bᵀ adj(M) 1` identity, and a
short scalar numerator certificate. The remaining open item is the analogous
`√15` bridge for `rkGaussLegendre3`.

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

This recipe does **not** transfer directly to `rkGaussLegendre3`. The
remaining tableau has:

- `Real.sqrt 15` in `rkGaussLegendre3.A` (entries like
  `2/9 - Real.sqrt 15 / 15`).

The matrix is **not** triangular: every off-diagonal entry is non-zero,
so the `Matrix.det_fin_three` expansion produces six terms with
`Real.sqrt 15` factors.
The resulting determinant identity

```
det (1 - z • A) = gl3Q z / 120          -- = (120 - 60z + 12z² - z³) / 120
```

is true (this is a classical fact: collocation methods produce Padé
denominators with rational coefficients, with all `√15` cross terms
cancelling), but
proving it in Lean requires algebraic manipulation modulo
`Real.sqrt 15 ^ 2 = 15`.

A straight `simp [Matrix.det_fin_three]; ring` does not close the identity
because `Real.sqrt 15` is not a polynomial atom. `ring` treats it as an
opaque variable, so any cancellation that depends on
`(Real.sqrt 15)^2 = 15` is invisible to `ring`.

Cycle 653 showed that the robust path is to split the proof into determinant
and adjugate-sum certificates, then finish with a short scalar numerator
calculation.

A short attempt during cycle 652 hit a `simp` stack overflow when
trying to unfold `Matrix.one_apply` together with `Fin (3)` decidable
equality on dense algebraic RK tableaux — the search blew through the heartbeat
budget before producing a tractable goal. That suggests the bridge
needs a more controlled rewrite chain than `simp only [..., rkGaussLegendre3,
Matrix.one_apply, ...]`.

## Context

Existing classical scalar A-stability:
- `OpenMath/GaussLegendre3.lean:198` — `gl3_aStable z hz : ‖gl3StabilityFn z‖ ≤ 1`

GLM iff bridge consumed:
- `OpenMath/RKAsGLM.lean:94` — `ButcherTableau.toGLM_isAStable_iff`

What remains to land:

```lean
theorem rkGaussLegendre3_stabilityFunction_eq (z : ℂ) (hz : z.re ≤ 0) :
    rkGaussLegendre3.stabilityFunction z = gl3StabilityFn z := ...
```

After which the GLM transport is one-line:

```lean
theorem rkGaussLegendre3_toGLM_isAStable : rkGaussLegendre3.toGLM.IsAStable := by
  rw [ButcherTableau.toGLM_isAStable_iff]
  intro z hz
  rw [rkGaussLegendre3_stabilityFunction_eq z hz]
  exact gl3_aStable z hz
```

## What was tried

- `Matrix.det_fin_three` followed by `simp only [..., Matrix.one_apply,
  rkGaussLegendre3, ...]` to unfold the determinant. The `simp` call looped
  / stack-overflowed when `if h : (i = j) then 1 else 0` from
  `Matrix.one_apply` was combined with `Fin 3` decidable equality and
  a dense algebraic tableau unfold.
- A manual `if_false` injection via `show ((0 : Fin 3) = (1 : Fin 3))
  ↔ False from by decide` followed by `simp only [..., if_false]`
  pre-simplified the diagonal pattern but still failed to close the
  determinant identity in a `ring` step because of the opaque square-root
  atom.

## Possible solutions

1. **Split linear-combination certificate.** Follow cycle 653:
   prove `det M`, prove `bᵀ adj(M) 1`, then prove the scalar numerator
   identity using `hs15_C : ((Real.sqrt 15 : ℝ) : ℂ) ^ 2 = 15`.
2. **Structured matrix decomposition.** Decompose `A = A₀ + sqrt15·A₁`
   into rational and irrational parts. Then `det(1 - zA) = det(1 -
   zA₀ - z·sqrt15·A₁)`, which can be expanded as a polynomial in
   `sqrt15` whose `(sqrt15)²` terms collapse via `sqrt15² = 15`. This may
   give a cleaner proof structure than a single `linear_combination`.
3. **Direct evaluation via Padé identity.** Use the fact that
   collocation methods produce stability functions equal to the
   diagonal Padé approximant (Iserles Theorem 4.6 / Hairer–Wanner
   Theorem IV.5.4). If a generic `collocation_stabilityFunction` 
   identity is available in `OpenMath/Collocation.lean`, the bridge
   becomes a corollary. Worth checking — `OpenMath/Pade.lean` already
   has Padé apparatus.

## Suggested next cycle

Use the cycle 653 Radau IIA proof as the template for GL3. Compute the two
`√15` certificate polynomials with exact rational arithmetic, then keep the
Lean proof split into determinant, adjugate-sum, and scalar numerator steps.
