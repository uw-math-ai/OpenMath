# Cycle 426 Results

## Worked on

Generic Adams–Bashforth `s`-step scalar convergence abstraction
(`OpenMath/LMMABGenericConvergence.lean`), per the cycle-426 strategy
(Step 1 primary task).

## Approach

1. **Aristotle bundle triage (Step 0)**: Both ready bundles target work
   that is already closed on `main` (cycle 425 closed the AB6 vector chain;
   the AB3 vector chain has been closed since cycle 412). Neither was
   downloaded or transplanted. No `OpenMath/TaylorBounds.lean` introduced.

2. **Sorry-first scaffold**: Wrote `OpenMath/LMMABGenericConvergence.lean`
   with the three named declarations (`abIter`, `abIter_lipschitz_one_step`,
   `ab_global_error_bound_generic`) plus supporting infrastructure
   (`abLip`, `abErr`, `abErrWindow`, `abResidual`, `abIter_step`,
   `abLip_window_bound`, `abResidual_bound_mono`). Confirmed with
   `lake env lean OpenMath/LMMABGenericConvergence.lean` that the file
   elaborates with two sorries (one-step Lipschitz, headline).

3. **Headline closed via Grönwall**: Closed
   `ab_global_error_bound_generic` directly using
   `lmm_error_bound_from_local_truncation` from
   `OpenMath/LMMTruncationOp.lean`, threading the residual hypothesis
   through the window-max recurrence supplied by
   `abIter_lipschitz_one_step`.

4. **Lipschitz one-step closed manually**: Wrote the window-max
   `(1 + h · Λ)`-recurrence proof from scratch, using the new
   `abIter_step` unfolding lemma, per-summand Lipschitz bounds, and
   `Finset.abs_sum_le_sum_abs` / `Finset.sum_le_sum` for the sum
   manipulation. Used the AB2 (cycle 408) one-step proof shape as the
   reference template, generalising the two-term `(3/2, -1/2)` algebra to
   a `Fin s`-indexed sum.

5. **Aristotle batch not submitted**: Both target sorries closed during
   manual proof work, so nothing remained to submit. The file is fully
   sorry-free at end of cycle.

## Result

SUCCESS — the "best" tier of the cycle-426 acceptance criteria.

`OpenMath/LMMABGenericConvergence.lean` exists, elaborates,
`lake build OpenMath.LMMABGenericConvergence` completes cleanly, and the
file is sorry-free. All three named declarations from the strategy are
present and closed:

- `LMM.abIter` — generic AB `s`-step iteration (well-founded recursion on
  the index, falls back to `0` for `s = 0`).
- `LMM.abIter_lipschitz_one_step` — window-max
  `(1 + h · Λ)`-recurrence with `Λ = L · ∑ |α_j|`.
- `LMM.ab_global_error_bound_generic` — headline applying
  `lmm_error_bound_from_local_truncation` once `|τ_n| ≤ K · h^(p+1)` is
  supplied as a hypothesis.

Plus reusable helpers extracted along the way: `abIter_step`,
`abLip_window_bound`, `abResidual_bound_mono`, `abErrWindow_nonneg`.

## Dead ends

- Initial attempt at a direct `unfold abIter` on the recurrence target
  unfolded both sides simultaneously into nested if-then-else trees,
  which made `congr` rewrites diverge. Switched to
  `conv_lhs => rw [abIter]` followed by `dif_neg`/`dif_pos` selection,
  which gave a clean single-step unfolding.

- A `ring_nf` inside a chained `rw` for the
  `∑ |α_j| · L · EN_n = (∑ |α_j|) · L · EN_n` step landed on a
  reordering Lean did not consider definitionally equal. Replaced with
  two applications of `← Finset.sum_mul` to pull `EN_n` and then `L`
  out of the sum.

## Discovery

- Well-founded recursion on `ℕ` with a `Fin s` body works cleanly via
  `termination_by n => n`; the per-`j` decreasing proof needs only
  `omega` once the `n < s` and `0 < s` branches are in scope.
- `Finset.le_sup' (b := ⟨k, _⟩) (Finset.mem_univ _)` is the cleanest way
  to access an individual window-slot bound without unfolding
  `abErrWindow`.
- The window-max one-step bound separates cleanly into "in-window"
  (`j + 1 < s`, bound by `EN n`) and "fresh-step" (`j + 1 = s`, bound
  by `(1 + h·Λ)·EN n + |τ_n|`) cases. This decomposition mirrors the
  AB2 `max(en1, en2)` split exactly.

## Suggested next approach

The deferred follow-ups from the cycle 426 strategy are now ripe:

1. **Vector mirror**: write `LMM.abIterVec` /
   `LMM.abIter_lipschitz_one_step_vec` /
   `LMM.ab_global_error_bound_generic_vec` in the same finite-dimensional
   normed-vector setting used by the existing AB`s`Vec chains.

2. **Refactor AB2–AB6 to flow through the abstraction**: each per-`s`
   chain becomes (a) the Taylor residual ladder bound `|τ_n| ≤ K · h^(p+1)`
   and (b) one application of `ab_global_error_bound_generic`. The
   per-`s` window-max one-step bound proofs (currently 200+ lines each)
   become redundant.

3. **Generic order-`p` Taylor residual bound from `ContDiff`**: still
   deferred — the per-order Taylor ladders differ in micro-detail across
   orders 2…7 and the strategy explicitly flags this as a multi-cycle
   research item.

The first follow-up (vector mirror) is the lowest-risk and would slot
cleanly into a single cycle.

## Aristotle bundle triage detail

- Project `9476c9e2-6000-4aa9-973d-b9ea1e103ac8`
  → `LMMAB6VectorConvergence.lean`. **REJECTED**: AB6 vector chain
  closed manually in cycle 425;
  `OpenMath/LMMAB6VectorConvergence.lean` already exposes
  `LMM.ab6Vec_global_error_bound` with no sorries (verified by `grep`).
- Project `893afb82-6924-4c6b-8892-4546226311c8`
  → `job_d_ab3Vec_pointwise_residual_bound.lean` plus a stray
  `TaylorBounds.lean`. **REJECTED**: AB3 vector chain has been closed
  on `main` since cycle 412
  (`LMM.ab3Vec_global_error_bound` in
  `OpenMath/LMMAB3Convergence.lean`); the strategy explicitly forbids
  introducing a free-floating `OpenMath/TaylorBounds.lean`.

Neither bundle was downloaded/extracted into the source tree.

## Aristotle batch this cycle

No new Aristotle batch submitted. Both target sorries (one-step
Lipschitz, headline) closed manually during the cycle. Documenting per
the strategy: there were no remaining sorrys to submit, so a batch
submission would have been a no-op.
