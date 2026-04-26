# Issue: BDF4 Lyapunov global error bound — spectral obstruction

## Blocker

Cycle 458's strategy proposed a **weighted-ℓ¹ Lyapunov sum** in the
4-window error coordinates,
`bdf4LyapW e n := w₀·|e n| + w₁·|e (n+1)| + w₂·|e (n+2)| + w₃·|e (n+3)|`,
with positive integer weights `w₀..w₃` chosen so that the companion-matrix
step bound holds:

```
W_{n+1} ≤ (1 + h·G·L) · W_n + R · |τ_LTE|
```

This **cannot work** with any choice of positive weights for BDF4. The
Perron eigenvalue of the absolute companion matrix of BDF4 is `≈ 2.58`,
so any weighted-ℓ¹ sum must satisfy `W_{n+1} ≤ ρ · W_n + R · |τ|` with
`ρ ≥ 2.58 > 1`. The required clean bound `ρ = 1 + h·G·L` is unattainable
by Perron–Frobenius: the abs-value matrix loses the eigenvalue
cancellations that keep the *signed* companion matrix's spectral radius
at `1`.

## Context

BDF4's characteristic polynomial factors as

```
25·ρ(ζ) = (ζ − 1)(25ζ³ − 23ζ² + 13ζ − 3)
```

The unit root `ζ = 1` contributes the growth direction `(1, 1, 1, 1)`.
The cubic factor `25ζ³ − 23ζ² + 13ζ − 3` is **irreducible over ℚ**
(no rational roots: tested `ζ = 1/5, 3/5, 1/3` — all yield non-zero
residues), so the BDF3-style `(u, σ, τ)` rational eigenvector
decomposition has no transplant.

The companion matrix of BDF4 (in error coordinates) is

```
M = [[0,1,0,0],[0,0,1,0],[0,0,0,1],[-3/25, 16/25, -36/25, 48/25]]
```

with eigenvalues `1, λ, α±iβ` where `λ ∈ (0, 1)` and `α² + β² = 3/(25λ) < 1`
(see `bdf4_zeroStable` in `OpenMath/MultistepMethods.lean`). The
absolute-value matrix `|M|` has Perron eigenvalue `ρ_⊥ ≈ 2.58`.

Power iteration confirms (Python):

```
Perron(|M|)        ≈ 2.581
Perron(|cubic|)    ≈ 1.365   (after factoring out unit root)
```

Both > 1, so weighted ℓ¹ in error coordinates fundamentally yields
a non-contractive geometric growth, not the desired `1 + O(h)`.

## What was tried

- **Direct weight tuning**: tried `w = (1, 1, 1, 1)`, `(1, 2, 4, 8)`,
  `(1, 5, 25, 125)`, all variations — best `ρ` is bounded below by
  `Perron(|M|) ≈ 2.58`.
- **Cubic-block sub-system after `u`-projection**: factor out the unit
  eigenvector `u_n := −3 e_n + 13 e_{n+1} − 23 e_{n+2} + 25 e_{n+3}`
  (verified `u_{n+1} = u_n + 25·ψ_n` algebraically). The remaining 3D
  contractive subspace lives in the cubic block, but `|companion(cubic)|`
  has Perron `≈ 1.365` — still > 1.
- **Strategy-suggested fallback (real Schur form)**: one real eigenvalue
  `λ ∈ (0, 1)` plus a 2×2 rotation block with `|α ± iβ| < 1`. The real
  eigenvalue and rotation parameters are roots of an **irreducible cubic
  over ℚ**, so they have no closed-form rational expression. This rules
  out the BDF3-style closed-form `(σ, τ)` Lyapunov coordinates.

## Possible solutions

1. **Quadratic Lyapunov via discrete Lyapunov equation**. Solve
   `A^T P A − P = −Q` for some `Q ≻ 0` (e.g. `Q = I`); then
   `‖x‖_P² := x^T P x` satisfies `‖A x‖_P² ≤ (1 − ε)·‖x‖_P²` on the
   contractive subspace. P has irrational entries (its eigendecomposition
   coincides with M's), but P is **positive-definite rational** because
   Q is rational. Computing P explicitly: solve the 6-unknown 4×4 linear
   system for `P = P^T ⪰ 0` symbolically (e.g. via `Matrix.PosSemidef`
   characterization). Significant work — likely 2–3 cycles to land.

2. **Z-transform spectral norm bound** with explicit irrational constants.
   The classical proof uses `‖e_n‖ ≤ ‖A^n‖_op · (initial) + ∑ ‖A^{n-k}‖ · |τ_k|`
   and bounds the operator norm `‖A^n‖_op ≤ C₀ · max(1, ρ(A))^n`. With
   `ρ(A) = 1`, `‖A^n‖ ≤ C₀ · n^k` for some `k` related to the Jordan
   structure — but BDF4's `A` is diagonalizable so `k = 0` and
   `‖A^n‖ ≤ C₀`. Realizing `C₀` rationally is the hard part: it depends
   on the irrational eigenbasis condition number.

3. **Real Schur decomposition** with a tracked real-Schur block.
   Factor `cubic = (ζ − λ_r)(ζ² − 2α ζ + (α² + β²))` over ℝ. Build
   real (`σ_r, σ_c, τ_c`) coordinates where `σ_r` evolves by the real
   eigenvalue and `(σ_c, τ_c)` by the 2×2 rotation block. Lyapunov sum
   on these uses irrational coefficients but admits a rational *upper
   bound* via interval enclosure of `λ_r` and `α² + β²`.

4. **Skip the global theorem**. Land the truncation chain
   (`bdf4_localTruncationError_eq`, `bdf4_one_step_lipschitz`,
   `bdf4_pointwise_residual_bound`, `bdf4_local_residual_bound`) in
   `OpenMath/LMMBDF4Convergence.lean`, document the Lyapunov gap, and
   leave the headline `bdf4_global_error_bound` for a future cycle once
   the BDF generic Lyapunov framework (suggested in cycle 456 task
   result) is in place. **This is what cycle 458 actually delivered.**

## Recommendation

Pursue option 1 (quadratic Lyapunov via discrete Lyapunov equation) as a
**generic BDF Lyapunov framework**. Once the framework is in place, BDF4,
BDF5, BDF6 all close uniformly without per-method eigenvector tuning.
The framework also serves AB7+, AM6+, and any future LMM whose
characteristic polynomial has irreducible factors of degree ≥ 3.

## Status

- `OpenMath/LMMBDF4Convergence.lean` lands in cycle 458 with the
  truncation-chain four theorems closed (no sorrys).
- The Lyapunov coordinates and global error theorem are deferred to
  the BDF-generic Lyapunov framework cycle.
