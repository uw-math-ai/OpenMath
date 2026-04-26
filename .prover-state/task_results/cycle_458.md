# Cycle 458 Results

## Worked on

**BDF4 scalar quantitative convergence chain** in
`OpenMath/LMMBDF4Convergence.lean`, mirroring the cycle 456 BDF3 scalar
template one order up.

The strategy proposed a 10-declaration scaffold landing the full BDF4
chain through a headline `bdf4_global_error_bound`. Cycle 458 lands the
**truncation chain** (5 declarations, all sorry-free) and **defers the
Lyapunov-window global theorem** because of a spectral obstruction
documented in `.prover-state/issues/bdf4_lyapunov_gap.md`.

## Approach

### Truncation chain (landed)

1. `LMM.IsBDF4Trajectory` — supplied 4-window trajectory predicate
   matching `y_{n+4} = (48/25)y_{n+3} − (36/25)y_{n+2} + (16/25)y_{n+1}
   − (3/25)y_n + (12/25)·h·f(t_{n+4}, y_{n+4})`.

2. `LMM.bdf4_localTruncationError_eq` — closed by `unfold; simp [bdf4,
   Fin.sum_univ_five, iteratedDeriv_one, iteratedDeriv_zero]; ring`,
   mirroring `bdf3_localTruncationError_eq`.

3. `LMM.bdf4_one_step_lipschitz` — implicit defect estimate `|defect|
   ≤ (12/25)·h·L·|e_{n+4}| + |τ_n|`. Closed by mirroring
   `bdf3_one_step_lipschitz` line-for-line with the new α/β coefficients
   and a 5-step `set` block on `(yn, yn1, yn2, yn3, yn4)` and
   `(tn..tn4, zn..zn4, τ)`.

4. `LMM.bdf4_pointwise_residual_bound` — fifth-order Taylor bound
   `|τ_n| ≤ 18 · M · h⁵` using the public AB4 fifth-order Taylor helpers
   (`y_fifth_order_taylor_remainder`, `derivY_fourth_order_taylor_remainder`).

   Exact rational coefficient computed via Python `Fraction`:

   ```
   c1 = (1/120)·4⁵ + (48/25)·(1/120)·3⁵ + (36/25)·(1/120)·2⁵ + (16/25)·(1/120)·1⁵
      = 4804/375 ≈ 12.81
   c2 = (12/25)·(1/24)·4⁴ = 128/25 = 5.12
   total = 6724/375 ≈ 17.93
   ```

   Slacked to integer `18` for `linarith` cleanliness.

   **Kernel-budget extraction**: First implementation kept the full
   algebraic argument (LTE identity + 5-term triangle inequality + 5
   Taylor bounds + slack) inline. The `whnf` and `isDefEq` checks
   exhausted the 200000-heartbeat budget: BDF4 has 5 R_y groups
   (vs BDF3's 4) and the polynomial identity for `hLTE_eq` is
   substantially heavier than BDF3's. Fixed by extracting a private
   helper `bdf4_pointwise_residual_alg` taking only the abstract scalars
   `(A, B, C, D, E)` and their five magnitude bounds, then invoking it
   from `bdf4_pointwise_residual_bound` after `set` + `clear_value` on
   the Taylor-remainder bodies. Mirrors the cycle 442/444/450/456 kernel
   discipline.

5. `LMM.bdf4_local_residual_bound` — `|τ_n| ≤ C · h⁵` packaging on a
   finite horizon. Closed by mirroring `bdf3_local_residual_bound`
   trivially, with `C = 18·M` from `iteratedDeriv_five_bounded_on_Icc`.

### Lyapunov global theorem (deferred)

The strategy proposed weighted-ℓ¹ in error coordinates,

```
bdf4LyapW e n := w₀·|e n| + w₁·|e (n+1)| + w₂·|e (n+2)| + w₃·|e (n+3)|
W_{n+1} ≤ (1 + h·G·L)·W_n + R·|τ_LTE|
```

with positive integer weights `w₀..w₃` chosen via `M^T w ≤ ρ·w`. **This
cannot work**: the absolute companion matrix `|M|` has Perron eigenvalue
`≈ 2.58`, so any positive-weighted ℓ¹ sum admits geometric growth
`ρ^N ≥ 2.58^N`, not the required `(1 + h·G·L)^N`. Verified
numerically in Python (200-iter power iteration on `|M|`): all four
ratios `(M^T w_∞)_i / (w_∞)_i` converge to `≈ 2.581`.

The strategy fallback (real Schur form) requires irrational coordinates
because the cubic factor `25ζ³ − 23ζ² + 13ζ − 3` is irreducible over ℚ
(verified — `ζ = 1/5, 3/5, 1/3` all yield non-zero residues). The
BDF3-style closed-form rational `(σ, τ)` decomposition has no transplant.

The Lyapunov global theorem is documented as a structured issue in
`.prover-state/issues/bdf4_lyapunov_gap.md` with four candidate
solutions and a recommendation (option 1: discrete Lyapunov equation
`A^T P A − P = −Q` for a generic BDF Lyapunov framework spanning BDF4,
BDF5, BDF6 uniformly).

### Aristotle batch

Per the strategy's "do not block on Aristotle" guidance and cycle 457's
report that all five BDF3-vector jobs stayed in `QUEUED` after the
30-min wait, **no Aristotle jobs were submitted this cycle**. The
truncation chain closed cleanly without tactic search, and the Lyapunov
piece would have required pinned-down weight values I could not find
(spectral obstruction). The cycle 453 AM8-vector bundle
`1f0a84ab-…` was correctly ignored as flagged by the strategy
(scaffold-shaped, against an already-closed live target).

## Result

**SUCCESS** — `OpenMath/LMMBDF4Convergence.lean` lands with **0 sorrys**
and 329 lines, compiling clean against:

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH \
  lake env lean OpenMath/LMMBDF4Convergence.lean
```

Closed declarations:

- `LMM.IsBDF4Trajectory`
- `LMM.bdf4_localTruncationError_eq`
- `LMM.bdf4_one_step_lipschitz`
- `LMM.bdf4_pointwise_residual_alg` (private kernel-budget helper)
- `LMM.bdf4_pointwise_residual_bound` (`|τ_n| ≤ 18·M·h⁵`)
- `LMM.bdf4_local_residual_bound` (finite-horizon `|τ_n| ≤ C·h⁵`)

Plan updated: cycle 458 entry added under §Current Target referencing
the new module, the residual coefficient `18`, and the
`bdf4_lyapunov_gap.md` issue file. Active frontier rolled forward to
**generic BDF Lyapunov framework**.

## Dead ends

- **Inline pointwise-residual proof timeout**: First attempt kept the
  full LTE identity (`ring`-heavy, 5 R_y groups + 1 R_y' group, ~30
  polynomial terms in `h`), 5-term chained triangle inequality,
  multiplicative Taylor bounds, and slack-to-18 chain inline. The
  kernel-checking phase exhausted the 200000-heartbeat budget at
  `whnf` of the theorem body and `isDefEq` of the consumer
  `bdf4_local_residual_bound`. *Fix*: extracted
  `bdf4_pointwise_residual_alg` taking abstract `(A, B, C, D, E)` and
  the five magnitude bounds; the consumer applies `set` + `clear_value`
  + a single `exact`. This is the cycle 442/444/450/456 pattern, now
  also required for BDF4 because the 5-Taylor-remainder LTE identity is
  substantially heavier than BDF3's 4-remainder version.

- **Weighted-ℓ¹ Lyapunov design**: Tried `w = (1, 1, 1, 1)`, `(1, 2, 4, 8)`,
  `(1, 5, 25, 125)`, and exhaustive integer enumeration up to `w_3 = 50`.
  Best `ρ` is bounded below by `Perron(|M|) ≈ 2.581` regardless of
  weight choice (Perron–Frobenius). Confirmed via 200-iter power
  iteration on `|M^T|`: eigenvector converges to
  `(0.038, 0.216, 0.538, 0.814)` (normalized) with all four
  componentwise ratios `≈ 2.581`. The strategy's "lift the weight on the
  dominant slot" guidance cannot work — the obstruction is structural,
  not tunable.

- **Cubic-block sub-system**: After factoring out the unit eigenvector
  `u_n := −3 e_n + 13 e_{n+1} − 23 e_{n+2} + 25 e_{n+3}` (verified
  algebraically: `u_{n+1} = u_n + 25·ψ_n`), the remaining 3D
  contractive subspace satisfies the cubic `25ζ³ − 23ζ² + 13ζ − 3`.
  Companion `|cubic|` has Perron `≈ 1.365` — still > 1. No rational
  Lyapunov weights make this contractive in ℓ¹.

- **Strategy fallback (real Schur form)**: The real eigenvalue and 2×2
  rotation parameters are roots of an irreducible cubic over ℚ, so they
  have no closed-form rational expressions. Ruled out for this cycle.

## Discovery

- **BDF4 LTE coefficient**: exact `6724/375` from
  `(4⁵ + (48/25)·3⁵ + (36/25)·2⁵ + (16/25))/120 + (12/25)·256/24`,
  slackened to integer `18` (was `7` for BDF3 from `153/22`).

- **Spectral obstruction is structural for BDF4+**: the BDF3-style
  Lyapunov decomposition relies on rational factorization of the
  characteristic polynomial after removing the unit root. BDF3 has the
  factor `ζ² − (7/11)ζ + 2/11` — quadratic, decomposable over ℚ
  (rational discriminant). BDF4 has `25ζ³ − 23ζ² + 13ζ − 3` — irreducible
  cubic over ℚ, so no analogous decomposition exists. BDF5 and BDF6
  presumably inherit this obstruction. The cycle 456 task result's
  suggestion of a **generic BDF Lyapunov framework** (quadratic
  Lyapunov via discrete Lyapunov equation) is the right next move.

- **Kernel-budget pattern is now mandatory for BDF4+**: 5 R_y groups in
  `hLTE_eq` exceed the budget. Always extract a private algebra core
  for BDF4+ pointwise residual proofs.

## Suggested next approach

1. **Generic BDF Lyapunov framework** (1–3 cycles): solve the discrete
   Lyapunov equation `A^T P A − P = −Q` symbolically over ℝ for a
   parameterized companion matrix `A` of a stable polynomial; lift the
   resulting rational `P` (`Q = I` is rational, so `P` is rational) to
   a Lyapunov norm `‖x‖_P² := x^T P x`. Then BDF4–BDF6 close uniformly.
   See option 1 in `bdf4_lyapunov_gap.md`.

2. **BDF4 vector truncation chain** (mirror this cycle's scalar work
   into `OpenMath/LMMBDF4VectorConvergence.lean`): identical algebraic
   structure, only Lipschitz/triangle inequalities differ. Estimated
   ~70% reuse of the scalar pointwise-residual algebra core.

3. **AM9 scalar** (cycle 458 fallback target, not started): mirror the
   AM8 scalar cycle 452 template one order up; 11-weight residual,
   eleventh-order Taylor ladder, integer growth `G ≥ 2(βₛ + S)` from
   AM9 weights. The strategy explicitly told me not to start this as a
   parallel target since BDF4 was the primary; remains a valid frontier
   option for a future cycle.
