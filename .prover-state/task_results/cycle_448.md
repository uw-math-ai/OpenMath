# Cycle 448 Results

## Worked on
Scalar BDF2 quantitative convergence chain in
`OpenMath/LMMBDF2Convergence.lean`, plus archival of two stale Aristotle
result directories that targeted already-closed `LMMAM6VectorConvergence.lean`.

## Approach
- Archived stale Aristotle dirs `67e400f2…` and `a8b33071…` to
  `.prover-state/aristotle_archive/` so the live scaffolds tree only
  reflects current work.
- Promoted three Taylor helpers in `OpenMath/LMMAB2Convergence.lean` from
  `private` to public (`iteratedDeriv_three_bounded_on_Icc`,
  `y_third_order_taylor_remainder`, `derivY_second_order_taylor_remainder`),
  giving the BDF2 chain access to them without re-proving.
- Wrote the BDF2 chain mirroring AM2 (2-step implicit) and BDF1 (1-step
  implicit) templates: `IsBDF2Trajectory`, `bdf2_localTruncationError_eq`,
  `bdf2_one_step_lipschitz`, `bdf2_pointwise_residual_bound`,
  `bdf2_local_residual_bound`, `bdf2_one_step_error_pair_bound`, and
  `bdf2_global_error_bound`.
- The pointwise residual is `τ = R_y(2h) − (4/3)·R_y(h) − (2h/3)·R_y'(2h)`
  (third-order remainders), summing to `(26/9)·M·h³`, slackened to `3·M·h³`.
- Used a Lyapunov decomposition (see "Discovery") to derive the clean
  `W_{n+1} ≤ (1 + h·(4L))·W_n + 6·|τ_n|` recurrence consumed by
  `lmm_error_bound_from_local_truncation`.

## Result
SUCCESS. `OpenMath/LMMBDF2Convergence.lean` compiles cleanly, no `sorry`,
no Aristotle batch needed (chain closed manually). Final headline:
`|y_N − y(t₀ + N·h)| ≤ 5·exp(4LT)·ε₀ + K·h²` with
`K = T·exp(4LT)·(6·C)`.

## Dead ends
- The strategy assumed a simple `(1 + h·G·L)`-recurrence with `G ∈ {4,5,6}`
  closes BDF2. It does not in the trivial max-norm: BDF2 has
  `|α₀|+|α₁| = 1/3 + 4/3 = 5/3 > 1`, so even at `h = 0` the max-norm
  growth factor is `5/3`. We had to switch to a Lyapunov norm before any
  `(1 + h·G·L)` form became available.
- First attempt at the algebraic chain used `nlinarith` for both
  `hgrowth_u/hgrowth_v` (ψ-bound coefficient slack) and the final
  combination. Both timed out; replaced with explicit `ring` + `linarith
  only` and the timeouts disappeared.
- `simp [hu_def, hv_def, hψ_def]; ring` to unfold `set` abbreviations
  pushed `whnf` over the heartbeat budget when the theorem grew. Replaced
  with explicit `show <unfolded>; ring`.
- A `rw [hid]` inside a `calc` step rewrote `e1` everywhere on both sides;
  fixed with `conv_lhs => rw [hid]`.

## Discovery
- BDF2 (and any LMM with `|α₀|+|α₁| > 1` aside from the leading 1) cannot
  use the AB-style max-norm `(1 + hGL)`-recurrence directly. Need a
  Lyapunov norm. Concretely, use eigen-coordinates of the companion
  matrix's `ρ`-roots `{1, 1/3}`:
  `u_n := (3/2)·e_{n+1} − (1/2)·e_n`,
  `v_n := (3/2)·(e_n − e_{n+1})`,
  with closed forms `u_{n+1} = u_n + (3/2)·ψ_n`,
  `v_{n+1} = (1/3)·v_n − (3/2)·ψ_n`, where
  `ψ_n := e_{n+2} − (4/3)·e_{n+1} + (1/3)·e_n` is the forcing.
- Under `(2/3)·h·L ≤ 1/4` we get `1/(1 − (2/3)·h·L) ≤ 4/3`, which lets us
  solve `|ψ| ≤ (8/9)·h·L·|u| + (8/81)·h·L·|v| + (4/3)·τ_abs`. Combined
  with `|u'| ≤ |u| + (3/2)|ψ|` and `|v'| ≤ (1/3)|v| + (3/2)|ψ|`, this
  gives `W_{n+1} ≤ (1 + 4·h·L)·W_n + 6·τ_abs`. Effective growth is `4L`,
  residual coefficient is `6`, initial factor is `5·ε₀`.
- The `(2/3)·h·L ≤ 1/4` small-step requirement (rather than the looser
  `≤ 1/2`) is essential for the Lyapunov analysis — it is the threshold
  at which `1/(1 − (2/3)·h·L) ≤ 4/3` becomes provable cleanly.
- For long theorems with many `set` abbreviations, prefer
  `linarith only [...]` over `linarith [...]`. The default form scans all
  hypotheses in scope, which becomes super-linear once you have ~30 named
  hypotheses; explicit `only` keeps the search small.
- `simp [hX_def]` to unfold `set` abbreviations is fragile when there are
  many of them. `show <fully unfolded body>` followed by `ring` is faster
  and predictable since `set` produces definitional equalities.

## Suggested next approach
- Cycle 449: BDF2 vector quantitative convergence chain
  (`OpenMath/LMMBDF2VectorConvergence.lean`), mirroring the BDF1 vector
  template but with the same Lyapunov sum
  `W_n := ‖(3/2)·e_{n+1} − (1/2)·e_n‖ + ‖(3/2)·(e_n − e_{n+1})‖`
  in the chosen vector norm. The same `(2/3)·h·L ≤ 1/4` small-step
  hypothesis carries over directly. Reuse
  `lmm_error_bound_from_local_truncation_vec` for the discrete Grönwall
  bridge.
- Cycle 450: AB7 or AM8 scalar quantitative convergence (Adams-family
  extension) — these stay in the trivial max-norm regime since
  `|α₀|+|α₁| = 1` for all Adams methods.
- Long-term: a generic LMM convergence wrapper that, given a Lyapunov
  norm and the algebraic forcing chain, derives the global bound, would
  unify BDF2/3/… and any other zero-stable LMM with `|α₀|+|α₁| > 1`.
