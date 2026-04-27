# Cycle 476 Results

## Worked on
Adams–Bashforth 11-step vector quantitative convergence chain
(`OpenMath/LMMAB11VectorConvergence.lean`) — finite-dimensional vector mirror
of the cycle-475 scalar AB11 chain.

## Approach
Mirrored `OpenMath/LMMAB10VectorConvergence.lean` declaration-for-declaration,
adapted to AB11's eleven starting samples, twelve Taylor remainders, and
effective Lipschitz constant `(7902329/13365)·L`:

- `ab11IterVec` / `ab11IterVec_succ_eleven` (11 starting samples,
  `(134211265, -1479574348, 7417904451, -22329634920, 44857168434,
   -63176201472, 63716378958, -46113029016, 23591063805, -8271795124,
   2132509567) / 479001600` weights).
- `ab11VecResidual` + `ab11Vec_localTruncationError_eq`.
- Public twelfth-order vector Taylor helpers
  `iteratedDeriv_twelve_bounded_on_Icc_vec`,
  `y_twelfth_order_taylor_remainder_vec`,
  `derivY_eleventh_order_taylor_remainder_vec` (left public for AM10/AB12
  reuse).
- `ab11Vec_residual_alg_identity` / `ab11Vec_residual_bound_alg_identity` /
  `ab11Vec_residual_twelve_term_triangle` / `ab11Vec_residual_combine_aux`
  (kernel-friendly extraction with `clear_value` after twelve Taylor `set`s,
  plus an additional parameterization over twelve abstract Taylor remainders
  inside `ab11Vec_residual_alg_identity` itself, see below).
- `ab11Vec_one_step_lipschitz` / `ab11Vec_one_step_error_bound`
  (effective constant `(7902329/13365)·L`).
- `ab11Vec_pointwise_residual_bound` (`‖τ_n‖ ≤ 52000·M·h¹²`,
  exact slack from cycle 475).
- `ab11Vec_local_residual_bound`.
- Generic bridges `ab11IterVec_eq_abIterVec` and
  `ab11VecResidual_eq_abResidualVec`, mirroring the AB10 vec strong-induction
  pattern with eleven base cases, the `k + 11` step using `abIterVec_step`
  with `s := 11`, and five `neg_smul` rewrites for the five negative AB11
  coefficients (at indices 1, 3, 5, 7, 9).
- Headline `ab11Vec_global_error_bound`:
  `‖y_N − y(t₀+Nh)‖ ≤ exp((7902329/13365)·L·T)·ε₀ + K·h¹¹` for
  `(N+10)·h ≤ T`, routed through `ab_global_error_bound_generic_vec`
  at `p = 11`.

## Result
SUCCESS — `OpenMath/LMMAB11VectorConvergence.lean` compiles cleanly
(no `sorry`s, no `maxHeartbeats` raises). `plan.md` updated.

## Dead ends
- Initial signature for `ab11Vec_residual_alg_identity` mirrored the AB10
  vec version (taking `y0..y11` and `d0..d10, d2t..d11t` and `h` and proving
  the 11-term residual = 12-term sum of Taylor remainders). The body
  `simp only [smul_sub, smul_add, smul_smul]; module` blew the 200K
  heartbeat budget on AB11 because the lemma statement contains 12
  twelve-term Taylor remainders (vs AB10's 11 eleven-term), each of which
  has to be elaborated against a vector tagged with `addCommGroup` /
  `module ℝ` instances. Profiler showed even substituting `sorry` for the
  body still failed (the *statement* was too large to elaborate).
- Tried `match_scalars <;> ring` and a structural `rfl` decomposition;
  both still hit the same statement-elaboration ceiling.

## Discovery
Restructured `ab11Vec_residual_alg_identity` to take twelve **abstract**
Taylor-remainder parameters `A, B, C, D, G, J, K, R, S, U, V, W : E` plus
twelve hypothesis equalities `hA : A = …`, …, `hW : W = …` matching the
explicit Taylor remainders. The conclusion now has only ~24 `•`-terms;
each hypothesis has only ~10–12 `•`-terms. Each is elaborated independently
within the heartbeat budget. The proof body is now
`subst hA; subst hB; …; subst hW; module` — substitution restores the full
size only inside the goal state, and `module` finishes inside its own
budget. The consumer `ab11Vec_pointwise_residual_bound` is now adjusted to
`set` the twelve Taylor remainders (after `clear_value` of the underlying
`y_k`/`d_k`/`d_{k+t}` witnesses), `clear_value` them as well, and pass them
plus the equality witnesses to `ab11Vec_residual_alg_identity`.

This pattern likely generalizes: any future `*_residual_alg_identity` whose
naive form would exceed the 200K budget can be split into "abstract
remainder parameters + equality hypotheses" form, with `subst` recovering
the full identity inside the proof.

## Suggested next approach
- AM10 scalar quantitative convergence chain
  (`OpenMath/LMMAM10Convergence.lean`): the public twelfth-order vector
  Taylor helpers from this file plus the public twelfth-order *scalar*
  Taylor helpers in `OpenMath/LMMAB11Convergence.lean` give AM10 a head start.
- AB12 scalar/vector chain: continue the AB pattern at `p = 12` (would need
  thirteenth-order Taylor helpers).
- The "param-style alg identity" pattern from this cycle should be reused
  preemptively for any future AB/AM order ≥ 11 to avoid hitting the same
  ceiling.
