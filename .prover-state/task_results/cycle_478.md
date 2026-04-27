# Cycle 478 Results

## Worked on

`OpenMath/LMMAM10VectorConvergence.lean` — the Adams–Moulton 10-step
**vector** quantitative convergence chain (vector mirror of the
cycle-477 scalar AM10 chain in `OpenMath/LMMAM10Convergence.lean`).
Headline: `LMM.am10Vec_global_error_bound` with growth `37L`,
residual coefficient `5045`, smallness `(134211265/479001600)·h·L ≤ 1/2`,
routed through `LMM.lmm_error_bound_from_local_truncation` at `p = 10`.

## Approach

Mirrored the AM9 vector chain (`OpenMath/LMMAM9VectorConvergence.lean`)
at AM10 weights, reusing the public twelfth-order vector Taylor helpers
from cycle-476's `OpenMath/LMMAB11VectorConvergence.lean`
(`iteratedDeriv_twelve_bounded_on_Icc_vec`,
`y_twelfth_order_taylor_remainder_vec`,
`derivY_eleventh_order_taylor_remainder_vec`).  The structure follows
the kernel-friendly extraction template established in cycles
442/444/450/466/468/473/476:

1. `IsAM10TrajectoryVec` (supplied implicit trajectory) +
   `am10VecResidual` + `am10Vec_localTruncationError_eq`.
2. `am10Vec_one_step_lipschitz` (vector AM10 contraction).
3. `am10Vec_one_step_error_bound` (divides out the implicit factor
   `(1 − (134211265/479001600)·h·L)`, growth `1 + h·37L`, residual
   slack `2·‖τ_n‖`); the slack identity
   `(1 − a·hL)(1 + h·37L) − (1 + b·hL) = (hL/479001600)(9099836030 − 4965816805·hL)`
   is closed by `ring` plus the `hsmall`-derived nonneg bound on
   `9099836030 − 4965816805·hL`.
4. `am10Vec_one_step_error_pair_bound` (10-window max-norm bound).
5. **Param-style algebraic identity** (`am10Vec_residual_alg_identity`)
   parameterized over twelve abstract Taylor witnesses (using
   `clear_value` after `set`) and the equality hypotheses extracted
   from the vector Taylor helpers; closed by `subst` + `module`,
   keeping the `module` elaboration well inside the 200K heartbeat
   budget — the same trick used in cycle 476's AB11 vector chain.
6. `am10Vec_residual_bound_alg_identity` (the ring identity
   `… = (251196920117213671/49792216320000)·M·h^12`).
7. `am10Vec_triangle_aux` / `am10Vec_residual_twelve_term_triangle`
   (12-term `norm_add_le` / `norm_sub_le` chain following the AM10
   sign decomposition `A − B − C − D + F − G + I − J + K − L + P − Q`,
   where the witness letters skip `E`/`H` to avoid clashing with the
   AB11-style scalar variable namespace).
8. `am10Vec_residual_combine_aux` (numerical slack
   `251196920117213671/49792216320000 ≤ 5045`, closed by `norm_num`).
9. `am10Vec_pointwise_residual_bound` (`‖τ_n‖ ≤ 5045·M·h^12`),
   `am10Vec_local_residual_bound`, `am10Vec_global_error_bound`.

## Result

**SUCCESS** — `lake env lean OpenMath/LMMAM10VectorConvergence.lean`
exits 0 with no warnings.

## Dead ends

- **First compile pass: simp/whnf timeout at the slack-identity
  linarith.**  The original `am10Vec_one_step_error_bound`
  used the same `simpa using mul_le_mul_of_nonneg_right` +
  `rw [hsplit]; linarith` template as `am9Vec_one_step_error_bound`.
  At AM10's bigger numerator scale (`8489011905/479001600` vs
  `78239681/7257600` for AM9) `linarith`'s internal `norm_num`
  normalization timed out at 200K heartbeats.  Fix: replaced the
  `simpa` with `le_mul_of_one_le_left` (no normalization needed)
  and the `rw [hsplit]; linarith` with an explicit two-step `calc`
  using `add_le_add hE_part hτ_part` followed by `hsplit.symm`.

- **Second compile pass: linarith failure at the global error
  bound's gronwall step.**  The vector residual lives at
  `‖τ_n‖ ≤ C·h^12`, but
  `lmm_error_bound_from_local_truncation` is invoked at `p = 10`
  (matching AM9 and the AM10 scalar headline `K·h^10`), so the
  per-step residual must be bounded by `(2C)·h^11`.  Without a
  small-step weakening, `(2C)·h^11 < 2·‖τ_n‖ ≤ (2C)·h^12` is
  consistent (when `h > 1`).  Fix: bumped `δ → min δ 1`, added
  `h_le_one : h ≤ 1` and `hh12_le_h11 : h^12 ≤ h^11` (one-line
  `calc` via `mul_le_mul_of_nonneg_left h_le_one`), and threaded
  the weakening through the `h2τ` derivation —
  exact mirror of the AM10 scalar version's lines 1120–1149.

## Discovery

- `le_mul_of_one_le_left` is a clean drop-in for the
  `simpa using mul_le_mul_of_nonneg_right hcoeff_le hxnn` pattern
  whenever the goal is `x ≤ a * x` from `1 ≤ a` and `0 ≤ x`.  It
  avoids `simp`/`linarith`'s internal normalization, which becomes
  the choke point at AM10's coefficient sizes.
- Splitting `linarith` on a multi-term factored inequality into a
  two-step `calc` (one `add_le_add` and one `hsplit.symm`) cuts the
  rational arithmetic burden dramatically and survived the 200K
  heartbeat budget at AM10 scale.

## Suggested next approach

The active frontier per `plan.md` line 343 is now: AB2–AB11 closed
scalar and vector; AM2–AM10 closed scalar and vector; BDF1–BDF3
closed scalar and vector; BDF4–BDF7 truncation only (BDF4–BDF6
deferred by `bdf4_lyapunov_gap.md`, BDF7 zero-unstable).  The next
natural target is **AM11 (11-step) scalar quantitative convergence
chain**, which would need the AM11 weights over the common
denominator (likely a multiple of `12!`), the AM11 implicit
recurrence under `|β_11|·hL ≤ 1/2`, and reused thirteenth-order
scalar Taylor helpers (which would have to be added in a sibling
file, since AB12 / AM11 share twelfth-derivative content but
need an extra Taylor order).  Alternatively the planner can pick
up AB12 scalar / AM11 vector / a Dahlquist-2 packaging task —
all are clean follow-ons given the current closed frontier.
