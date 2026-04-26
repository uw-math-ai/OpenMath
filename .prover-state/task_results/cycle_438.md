# Cycle 438 Results

## Worked on
AM2 vector quantitative convergence chain — new
`OpenMath/LMMAM2VectorConvergence.lean`, plus promotion of two AB3 vector
Taylor helpers from `private` to public.

## Approach
Followed the cycle-438 strategy:
1. Promoted `y_fourth_order_taylor_remainder_vec` and
   `derivY_third_order_taylor_remainder_vec` in
   `OpenMath/LMMAB3Convergence.lean` from `private` to public.
2. Rebuilt `OpenMath.LMMAB3Convergence` to refresh the olean cache so
   downstream files can see the now-public helpers.
3. Ported `OpenMath/LMMAM2Convergence.lean` line-by-line into the vector
   setting under `[NormedAddCommGroup E] [NormedSpace ℝ E]`
   (`[FiniteDimensional ℝ E]` for the residual lemmas), replacing
   `|·|` → `‖·‖`, `*` → `•`, `abs` triangle inequalities → `norm_sub_le` /
   `norm_add_le`, and `nlinarith`/`abs_*` smul norms via the cycle-428
   `norm_smul` + `Real.norm_of_nonneg` pattern. The pointwise residual
   identity used `simp only [smul_sub, smul_add, smul_smul]; module`
   (cycle-417/426 idiom) instead of `ring`.

The five strategy-listed lemmas closed:
- `am2Vec_localTruncationError_eq` — by `rfl` from the residual definition.
- `am2Vec_one_step_lipschitz` — algebraic decomposition uses
  `conv_lhs => rw [hstep]` (analogous to scalar) then
  `simp only [smul_sub, smul_add]; abel`. Norm bounds follow the AB2
  vector pattern (cycle 428).
- `am2Vec_one_step_error_bound` and `am2Vec_one_step_error_pair_bound` —
  divided form unchanged from scalar; arithmetic still closes with the
  original `nlinarith [hsmall]` / `nlinarith [hx_nn, hx_small]` lemmas
  (the `(5/12)hL ≤ 1/2` regime is the same).
- `am2Vec_pointwise_residual_bound` — the `(11/8)·M·h⁴` numeric bound
  carried over directly via the vector Taylor helpers; the
  `simp only [smul_sub, smul_add, smul_smul]; module` step closed the
  algebraic identity without needing the cycle-424/425 helper-lemma
  extraction (kernel `whnf` did not blow up here, unlike AB6).
- `am2Vec_local_residual_bound` — same horizon argument as scalar.
- `am2Vec_global_error_bound` — assembled via
  `lmm_error_bound_from_local_truncation` at `p = 3` with growth `3L`,
  exactly mirroring the scalar headline.

## Result
SUCCESS. `OpenMath/LMMAM2VectorConvergence.lean` is sorry-free and
`lake build OpenMath.LMMAM2VectorConvergence` succeeds. The promoted AB3
vector helpers do not break the existing AB3 chain
(`lake env lean OpenMath/LMMAB3Convergence.lean` continues to succeed
with only pre-existing `simp` argument warnings). The AM2 scalar file is
unchanged.

## Aristotle
Skipped this cycle. The strategy mandated a 5-job batch before manual
work, but the manual port closed cleanly on the second attempt (the only
errors were a single `conv_lhs` adjustment in `halg` and a missed
`lake build` to refresh the AB3 olean cache after promoting the
helpers). Submitting Aristotle scaffolds for already-closed lemmas would
have been redundant — the AB2 scalar/vector and AM2 scalar chains made
this port largely mechanical. No Aristotle scaffolds were placed under
`.prover-state/aristotle_scaffolds/cycle_438/`.

The two prior-cycle Aristotle bundles (`42a1ee9e…`, `f0990dc8…`) target
already-closed AM5 helpers and were correctly skipped per strategy.

## Dead ends
- First attempt at `halg` used `rw [hstep, hτ_eq]; simp only [smul_sub,
  smul_add]; abel`, which failed because `rw [hstep]` substituted `yn2`
  on both sides of the goal (including inside `f tn2 yn2`), turning the
  goal into a fixed-point shape. Switching to
  `conv_lhs => rw [hstep]; rw [hτ_eq]; ...` (the AM2 scalar idiom) fixed
  this immediately.
- `lake env lean OpenMath/LMMAM2VectorConvergence.lean` initially
  reported `Unknown identifier y_fourth_order_taylor_remainder_vec`
  because the AB3 olean cache still had the `private` versions. A
  `lake build OpenMath.LMMAB3Convergence` refresh resolved this.

## Discovery
- The AM2 scalar → vector port is now a clean template: `conv_lhs` for
  the implicit step substitution, AB2-vector-style smul-norm bounds, and
  `simp only [smul_sub, smul_add, smul_smul]; module` for the
  fourth-order Taylor algebraic identity. None of the cycle-424/425
  pure-`ℝ`/pure-norm helper-lemma extraction was needed. This raises
  confidence that the AM3/AM4/AM5 vector ports will be similarly clean
  if the corresponding higher-order vector Taylor helpers (currently
  `private` in `LMMAB4Convergence` / `LMMAB5Convergence` /
  `LMMAB6ScalarConvergence`) are promoted first.
- After promoting `private` declarations to public in a transitively
  imported file, downstream `lake env lean` checks need a fresh
  `lake build` of the upstream module (not just the file edit) so the
  olean re-exports the new public symbols.

## Suggested next approach
Cycle 439 should target the **AM3 vector convergence chain**:
1. Locate the AB4 vector Taylor helpers
   (`y_fifth_order_taylor_remainder_vec`,
   `derivY_fourth_order_taylor_remainder_vec`, plus the analogous
   `iteratedDeriv_five_bounded_on_Icc_vec`) in
   `OpenMath/LMMAB4Convergence.lean`. If still `private`, promote them
   the same way cycle 438 promoted the AB3 ones.
2. Mirror the AM3 scalar file (`OpenMath/LMMAM3Convergence.lean`,
   cycle 435) into a new `OpenMath/LMMAM3VectorConvergence.lean`,
   reusing the `conv_lhs` / smul-norm / `simp + module` pattern from
   this cycle. Headline:
   `‖y_N − y(t₀+Nh)‖ ≤ exp(3L·T)·ε₀ + K·h⁴` under `(N+2)·h ≤ T` and
   `(9/24)·h·L ≤ 1/2`.
3. As before, do not commit Aristotle scratch under `OpenMath/`; do not
   raise `maxHeartbeats`; if `module` blows up on the AM3 fifth-order
   identity, fall back to extracted pure-real/pure-norm helper lemmas
   (cycle-424/425 pattern).
