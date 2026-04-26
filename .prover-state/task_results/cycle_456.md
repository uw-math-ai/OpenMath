# Cycle 456 Results

## Worked on
Closing the BDF3 scalar quantitative convergence chain in
`OpenMath/LMMBDF3Convergence.lean`. Built on the cycle-453 declarations
(`IsBDF3Trajectory`, `bdf3_localTruncationError_eq`, `bdf3_one_step_lipschitz`,
`bdf3_pointwise_residual_bound`, `bdf3_local_residual_bound`) and added the
Lyapunov-window step recurrence `bdf3_one_step_error_bound`, the initial-state
and projection helpers, and the headline `bdf3_global_error_bound`.

## Approach

### Lyapunov coordinates

Companion matrix of `ρ(ζ) = ζ³ − (18/11)ζ² + (9/11)ζ − (2/11)
  = (ζ−1)(ζ² − (7/11)ζ + 2/11)` has principal root `1` and a complex pair with
`|λ|² = 2/11`. Project the 3-window error `(e_n, e_{n+1}, e_{n+2})` onto
eigenvectors:

* `u_n := (2/11) e_n − (7/11) e_{n+1} + e_{n+2}` (left eigenvector for λ=1).
* `σ_n := (1/6)(4 e_n + 7 e_{n+1} − 11 e_{n+2})` and
  `τ_n := (1/6)(−2 e_n + 13 e_{n+1} − 11 e_{n+2})` (complementary V-coordinates).

These satisfy *exact* coordinate recurrences (no Lipschitz slack; pure algebra
at the trajectory level):

* `u_{n+1} = u_n + ψ_n`
* `σ_{n+1} = τ_n − (11/6) ψ_n`
* `τ_{n+1} = −(2/11) σ_n + (7/11) τ_n − (11/6) ψ_n`

where `ψ_n = e_{n+3} − (18/11) e_{n+2} + (9/11) e_{n+1} − (2/11) e_n` is the
defect. Verified by `unfold` + `push_cast` + `ring`.

The Lyapunov sum is

```
W_n := |u_n| + (1/11) (|σ_n| + 5 |τ_n|)
```

with weight `γ = 5` on the `τ` band. The choice `1/11` and `γ = 5` was tuned so
that the algebraic step bound

```
W_{n+1} ≤ (1 + h·(6 L)) W_n + 4 |τ_LTE,n|
```

is *clean* (small integer coefficient `4`, growth constant `6L`) under the
small-step regime `(6/11) h L ≤ 1/4`.

### Inversion identity

To convert `W_n` back to a per-index error bound,

```
e_{n+2} = (11/6) u_n + (-2/11) σ_n + (7/11) τ_n
```

(verified by `ring`; the inverse matrix has determinant 1). Triangle inequality
gives `|e_{n+2}| ≤ (11/6)|u| + (2/11)|σ| + (7/11)|τ| ≤ 2 W_n`, since
`11/6 ≤ 2`, `2/11 ≤ 2/11`, and `7/11 ≤ 10/11 = 5·(2/11)`.

### Initial bound

If `|e_0|, |e_1|, |e_2| ≤ ε₀`:

* `|u_0| ≤ (2/11 + 7/11 + 1) ε₀ = 20/11 ε₀`
* `|σ_0| ≤ (4 + 7 + 11)/6 ε₀ = 22/6 ε₀`
* `|τ_0| ≤ (2 + 13 + 11)/6 ε₀ = 26/6 ε₀`

So `W_0 ≤ 20/11 + (1/11)(22/6 + 5·26/6) = 20/11 + 76/33 = 136/33 ≈ 4.12 ε₀`,
upper-bounded by `5 ε₀`.

### Global theorem

Following the BDF2 template (`bdf2_global_error_bound`):

* Apply `lmm_error_bound_from_local_truncation` with `L → 6L`, `C → 4C`, `p = 3`
  on the Lyapunov sum `W` (which is non-negative and obeys the right step
  recurrence after multiplying the LTE bound `|τ_LTE,n| ≤ C h^4` by 4).
* `W_0 ≤ 5 ε₀` ⇒ `W_{N''+1} ≤ 5 exp(6L·T) ε₀ + (4C)·T·exp(6L·T)·h^3`.
* For `N = N''+3`, `|e_N| = |e_{(N''+1)+2}| ≤ 2 W_{N''+1}`, giving the
  headline `|e_N| ≤ 10 exp(6L·T) ε₀ + 8·T·exp(6L·T)·C·h³`.
* `N = 0, 1, 2` cases handled directly (`|e_N| ≤ ε₀ ≤ 10 exp(6L·T) ε₀ + K h³`).

Constraint `(N+2)·h ≤ T` matches the 3-window structure.

## Result
SUCCESS — `OpenMath/LMMBDF3Convergence.lean` compiles cleanly with **0
sorrys** (only two pre-existing unused-variable lints in
`bdf3LyapU_succ_eq`).

Closed declarations added in cycle 456:

* `bdf3LyapSigma_succ_eq`, `bdf3LyapTau_succ_eq` (per-coordinate exact
  recurrences)
* `bdf3_one_step_lyapunov_alg` (private 8-scalar pure-algebra core)
* `bdf3_one_step_error_bound` (thin wrapper, ~70 lines)
* `bdf3LyapW_initial_bound` (`W_0 ≤ 5 ε₀`)
* `bdf3_eIdx2_le_W` (`|e_{n+2}| ≤ 2 W_n`)
* `bdf3_global_error_bound` (headline `|y_N − y(t₀+Nh)| ≤ 10·exp(6L·T)·ε₀ + K·h³`)

Constants: growth constant `G = 6` (smallest integer ≥ 11/2), residual
prefactor `K = 8·T·exp(6L·T)·C`, prefactor on `ε₀` is `10`.

## Dead ends

* **Inline kernel timeout**: First implementation kept the full algebraic
  Lyapunov argument inline inside `bdf3_one_step_error_bound`. Even after
  replacing two `nlinarith` calls with explicit `ring`-based difference
  identities, the kernel budget was still exhausted by the heavy ambient
  context (yseq, y, hy, hyf, f, hf, t₀, n + many local abbreviations).
  *Fix*: Extracted into private `bdf3_one_step_lyapunov_alg` taking only
  8 abstract scalars and `clear_value`-d the `set` block, mirroring the
  cycle 442/444/450 pattern.

* **Aristotle batch deemed unnecessary**: Strategy proposed batching ~5
  Aristotle jobs after a sorry-first scaffold. After writing the scaffold
  the algebraic helper extraction made all sub-proofs tractable manually
  (no tactic search needed beyond `nlinarith` + structured triangle
  inequalities), so I closed the chain inline. The `a2b23ad4-…` bundle
  was rejected as instructed (targets the already-closed AM8 vector chain).

* **`Σ` / `Τ` as `set` names**: Lean 4 reserves `Σ` (BigOperator). Renamed
  to `Sval`, `Tval`, `Uval`. Kept the unicode in the documentation comments
  but not in code identifiers.

* **`abs_add` identifier**: Mathlib uses `abs_add_le` in current naming.
  Replaced 4 occurrences.

## Discovery

* The clean Lyapunov sum `W := |u| + γ_σ |σ| + γ_τ |τ|` for BDF-class methods
  with complex eigenvalues admits *integer-rational* growth constants when
  `γ_σ, γ_τ` are tuned to absorb the worst-case algebraic blow-up at each
  index. For BDF3, `γ_σ = 1/11`, `γ_τ = 5/11` works; the resulting bound
  has growth `6L` (vs. raw bound `~7.4 L`), with an integer step coefficient
  `4` on the LTE term.

* Pure-algebra helper extraction is now a reliable cycle-460 pattern. The
  helper takes 6 ≤ `n_args` ≤ 12 abstract scalars, all step-bound hypotheses,
  and a single algebraic conclusion. The wrapper is a thin `set` + `apply`
  + `rw` of three coordinate `succ_eq` lemmas. Time investment: ~40% on
  the algebra core, ~20% on the inversion identity, ~40% on global theorem
  case-split.

* `nlinarith` with `clear_value` closes the algebraic `W` step bound in
  one shot once `|en3|` is replaced by `(11/6)|u| + (2/11)|σ| + (5/11)|τ|`
  and the `(6/11)·h·L ≤ 1/4` slack is folded in. Cycle budget kept well
  under 200000 heartbeats.

## Suggested next approach

* **BDF3 vector quantitative convergence**: mirror the scalar chain in
  `OpenMath/LMMBDF3VectorConvergence.lean`, using `‖·‖` instead of `|·|`
  and `‖f t a − f t b‖ ≤ L · ‖a − b‖`. The Lyapunov coordinates and
  algebraic identities are identical; only Lipschitz/triangle inequalities
  differ. Estimated cost: 70% reuse of cycle-456 algebra core.

* **AM8 vector global theorem**: still pending. Cycle 454 closed the AM8
  scalar global theorem and the AM8 vector convergence chain through the
  one-step bound; the final headline AM8 vector global theorem is the next
  Adams-family target.

* **BDF4 / BDF5 / BDF6 quantitative convergence**: BDF3 scaled ζ-eigenvalues
  through `|λ|² = 2/11`. BDF4 has more involved eigenstructure (degree-4
  characteristic polynomial); a generic BDF Lyapunov-coordinate framework
  may be required.
