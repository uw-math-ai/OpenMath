# Cycle 469 Results

## Worked on
AB9 vector quantitative convergence in `OpenMath/LMMAB9VectorConvergence.lean`,
plus the corresponding `plan.md` frontier update.

## Approach
I verified that the tenth-order vector Taylor helper names requested by the
planner are public, then mirrored the AB8 vector chain and scalar AB9 chain:

- `LMM.ab9IterVec` and `LMM.ab9VecResidual`.
- `LMM.ab9Vec_localTruncationError_eq`.
- `LMM.ab9Vec_one_step_lipschitz` and `LMM.ab9Vec_one_step_error_bound`.
- Generic bridge lemmas `LMM.ab9IterVec_eq_abIterVec` and
  `LMM.ab9VecResidual_eq_abResidualVec`.
- Extracted residual helpers, including `ab9Vec_residual_combine_aux`, so the
  pointwise residual bound closes outside the heavy `set`/`clear_value`
  context.
- `LMM.ab9Vec_local_residual_bound` and the headline
  `LMM.ab9Vec_global_error_bound`.

The AB9 weights were checked against `OpenMath/LMMAB9Convergence.lean`, and the
same slack constant as scalar AB9 was used: exact residual coefficient
`102509448755347 / 20575296000`, slacked to `4983`.

I attempted the required Aristotle batch for:

- `LMM.ab9Vec_one_step_lipschitz`
- `LMM.ab9Vec_localTruncationError_eq`
- `ab9Vec_residual_ten_term_triangle`
- `LMM.ab9Vec_pointwise_residual_bound`
- `LMM.ab9VecResidual_eq_abResidualVec`

All five `submit_file` calls were rejected with HTTP 429 because the Aristotle
queue already had too many in-progress requests. I still slept for 1800 seconds
as required and then checked Aristotle once. The post-wait queue contained only
older BDF/Lyapunov jobs, so there were no cycle-469 Aristotle results to
incorporate.

## Result
SUCCESS. `OpenMath/LMMAB9VectorConvergence.lean` compiles with no `sorry`s and
no warnings from the file itself.

Verification completed:

- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMAB9VectorConvergence.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.LMMAB9VectorConvergence`
- `rg -n "by\\s+sorry|:=\\s*by\\s*admit|\\badmit\\b" OpenMath/*.lean`
- `lean_verify` on `LMM.ab9Vec_global_error_bound` reported only standard
  Mathlib axioms: `propext`, `Classical.choice`, and `Quot.sound`.

## Dead ends
Aristotle was unavailable for new cycle-469 jobs because the shared queue was
saturated. Manual proof work was therefore load-bearing for this cycle.

No BDF4-BDF6 Lyapunov work was attempted.

## Discovery
The AM8 vector tenth-order Taylor helpers are public and usable by importing
`OpenMath.LMMAM8VectorConvergence`.

The AB9 vector residual bound benefits from the same kernel-budget pattern as
cycle 468: keep the Taylor remainders abstract, call `clear_value`, then finish
with a separate combine lemma taking `A,B,C,D,G,J,K,R,S,U,M,h` and the ten
Taylor-bound hypotheses. This avoided putting the large scalar `linarith`
combination in the same context as the vector Taylor aliases.

## Suggested next approach
Continue the Adams-Bashforth frontier with the next scalar/vector pair, using
the combine-aux extraction from the start for any order with ten or more Taylor
remainder terms.
