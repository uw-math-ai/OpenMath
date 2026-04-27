# Cycle 480 Results

## Worked on
AB12 vector quantitative convergence chain in
`OpenMath/LMMAB12VectorConvergence.lean` (new file). Mid-restructuring
sorry-first scaffold targeting the AB12 vector deliverable to mirror cycle 476
(`LMMAB11VectorConvergence.lean`) with AB12 weights and one extra abstract
witness in the residual algebra identity.

## Approach
Wrote a fresh sorry-first scaffold (per the project's mandatory sorry-first
rule) with correct AB12 signatures throughout:

- Imports `LMMAB12Convergence` (scalar AB12, with `ab12GenericCoeff` /
  `abLip_ab12GenericCoeff` reused) and `LMMAB11VectorConvergence` (public
  twelfth-order vector Taylor helpers).
- `sum_univ_twelve_aux_vec : ∑ i : Fin 12, f i = f 0 + ... + f 11` (proved).
- `ab12IterVec` (12 starting samples `y₀..y₁₁`, recurrence on `n + 12` with
  AB12 weights `(4527766399, -19433810163, 61633227185, -135579356757,
  214139355366, -247741639374, 211103573298, -131365867290, 58189107627,
  -17410248271, 3158642445, -262747265) / 958003200`, leading at index
  `n+11`).
- 12 `ab12IterVec_<k>` simp lemmas for `k = 0..11` (rfl).
- `ab12IterVec_succ_twelve` (rfl).
- `ab12VecResidual` and `ab12Vec_localTruncationError_eq` (rfl) with the
  matching twelve-derivative residual.
- `iteratedDeriv_thirteen_bounded_on_Icc_vec` (proved via
  `IsCompact.exists_bound_of_continuousOn`).
- `ab12Vec_one_step_lipschitz` and `ab12Vec_one_step_error_bound` (proved by
  `abIter_lipschitz_one_step_vec hs ab12GenericCoeff hh hL hf t₀ … hyf n`
  followed by `rw [abLip_ab12GenericCoeff L]`).

The seven remaining `sorry`'s have correct AB12 signatures and are documented
as the cycle 481 frontier:

- `y_thirteenth_order_taylor_remainder_vec`
- `derivY_twelfth_order_taylor_remainder_vec`
- `ab12Vec_pointwise_residual_bound` (`‖τ_n‖ ≤ 162031·M·h¹³`)
- `ab12Vec_local_residual_bound`
- `ab12IterVec_eq_abIterVec`
- `ab12VecResidual_eq_abResidualVec`
- `ab12Vec_global_error_bound` (headline:
  `‖y_N − y(t₀+Nh)‖ ≤ exp((443892/385)·L·T)·ε₀ + K·h¹²`
  for `(N+11)·h ≤ T`).

The `ab12Vec_residual_alg_identity` lemma (parameterized abstract-remainder
pattern with thirteen abstract witnesses A..M) is signature-noted in a comment
block and intentionally left out of the file: an early attempt to inline it
hit a 200K-heartbeat `isDefEq` timeout during signature elaboration alone (its
type carries thirteen `(hX : … = …)` hypotheses with substantial right-hand
sides). The plan for cycle 481 is to port the AB11Vec pattern with one extra
witness, possibly across two helper lemmas if a single signature still
exceeds the budget.

Verified the file compiles via
`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean
OpenMath/LMMAB12VectorConvergence.lean`: emits seven `declaration uses
sorry` warnings and no errors.

Submitted one Aristotle batch attempt for the two Taylor remainders. Service
returned `429 You have too many requests in progress` (existing QUEUED jobs
from earlier in the day still in flight) — submission skipped per cycle 479's
established protocol.

## Result
PARTIAL SUCCESS — the AB12 vector chain landed as a compiling sorry-first
scaffold. Closed unconditionally:
- File structure with all 22 declarations and correct AB12 signatures.
- `sum_univ_twelve_aux_vec`.
- `ab12IterVec` definition + twelve `_zero..._eleven` simp lemmas + `_succ_twelve`.
- `ab12VecResidual`, `ab12Vec_localTruncationError_eq`.
- `iteratedDeriv_thirteen_bounded_on_Icc_vec`.
- `ab12Vec_one_step_lipschitz`, `ab12Vec_one_step_error_bound`.

Open sorries: the seven items listed above. plan.md updated with a `[ ]`
AB12 vector entry pinned to cycle 480 with explicit sorry frontier; once
cycle 481 closes the algebra identity and downstream consumers, this entry
becomes `[x]`.

## Dead ends
- An initial in-place port-via-substitution approach (Python text-rewrite of
  `LMMAB11VectorConvergence.lean` with AB11→AB12 identifier renames + a
  twelfth `y₁₁` argument) left the file in an intermediate state where
  identifier names matched AB12 but recurrence/weights/Taylor degrees still
  encoded AB11. Continuing along that path required structural surgery in
  every section (definition, recurrence, Taylor, algebra, consumers,
  bridges, headline). Abandoned in favour of writing a fresh sorry-first
  scaffold.
- The `ab12Vec_residual_alg_identity` signature with thirteen abstract
  witnesses (one more than AB11Vec's twelve) blew the 200K heartbeat budget
  during type elaboration with `:= True := by trivial`. Removed and noted as
  a comment block; cycle 481 should split it into two helper lemmas if a
  single signature still doesn't fit.
- Aristotle 429 in-progress quota: cycle 479's submission backlog plus other
  queued jobs (LMMAM10Convergence, LMMAB11Convergence) still in flight.

## Discovery
- The 13-abstract-witness signature for the residual algebra identity is the
  current ceiling under the cycle-476 parameterized abstract-remainder
  pattern: AB12Vec's identity needs witness `M` (h-step), `L` (2h),
  `K` (3h), …, `A` (12h-y0 difference). Either we (a) split it into two
  6-or-7 witness sub-identities and chain them via `linear_combination`, or
  (b) introduce a `Module`-style structure parameterized over a finite
  family of `Fin 13 → E` witnesses and prove the identity once
  abstractly. (b) is the more invasive change but would scale to AB13/AB14.
- Reusing the public twelfth-order vector Taylor helpers from AB11Vec
  (`y_twelfth_order_taylor_remainder_vec`,
  `derivY_eleventh_order_taylor_remainder_vec`) inside the new
  thirteenth-order vector Taylor helpers should mirror the scalar AB12
  pattern that fed off `y_eleventh_order_taylor_remainder` etc.
- The sign pattern shift between AB11 (β_10 leading positive) and AB12 (β_11
  leading positive, β_10 negative) means the leading recurrence sign flips
  every step — this is the source of all the per-term sign differences when
  porting weights.

## Suggested next approach
Cycle 481: close the seven AB12 vector sorries in order, prioritizing
(1) the residual algebra identity (split if needed),
(2) `ab12Vec_pointwise_residual_bound`,
(3) `ab12Vec_local_residual_bound`,
(4) the two bridge lemmas (mechanical Fin 12 substitution from cycle 476),
(5) the headline `ab12Vec_global_error_bound`. The two Taylor remainders can
be filled in parallel using the AB11Vec degree-12 versions wrapped one level
deeper. Aristotle should be batch-submittable once the existing queue drains
(re-check status before each submission attempt).

After AB12 vector closes, the next frontier is AM11 scalar (the
thirteenth-order scalar Taylor helpers exist in `LMMAB12Convergence`).
