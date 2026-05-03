# Cycle 712 Results

## Worked on
§521 Steps D.6 + D.7 + D.8 in `OpenMath/LMMAsGLM/StabilityCharpoly.lean`:

* `toGLM_stabilityMatrixPY_zero_charpoly_eval_zero` (Step D.6) —
  `(PY(0)).charpoly.eval 0 = α 0`.
* `toGLM_stabilityMatrixPY_zero_charpoly_eval_one` (Step D.7) —
  `(PY(0)).charpoly.eval 1 = 1 + ∑ α (castSucc l)`.
* `D_mul_toGLM_charpoly_eval_zero_concrete` (Step D.8) —
  fully concrete coefficient form of the cycle 708 ξ=0 identity.

## Approach
Followed the strategy template literally. Inserted all three theorems
in one `Edit` immediately before the `end LMM` marker on line 1839.

* D.6: closed-form expansion of cycle 694
  `toGLM_stabilityMatrixPY_zero_charpoly_eq` followed by
  `Polynomial.eval_sub` / `eval_pow` / `eval_X` /
  `eval_finset_sum`, then `Finset.sum_eq_single ⟨0, hs⟩` to isolate
  the surviving summand. Closed each branch with `simp` plus
  `zero_pow` for `k ≠ 0`.
* D.7: same charpoly-rewrite, simplifying `1^s = 1` and reducing
  the sum via a `Finset.sum_neg_distrib` rewrite, with each
  summand collapsing under `simp` on `eval_mul / eval_C / eval_pow /
  eval_X`. Closed by `ring`.
* D.8: pure substitution — three rewrites against
  `D_mul_toGLM_charpoly_eval_zero_eq` (cycle 708),
  `toGLM_stabilityMatrixPY_zero_charpoly_eval_zero` (D.6),
  and `rowFBetaPoly_eval_zero` (cycle 710 / D.4). Closed by `rfl`.

## Result
SUCCESS — file compiles cleanly with no errors and no warnings.
All three targets landed in one cycle.

## Dead ends
First-pass D.6 used the strategy's literal `· simp; push_cast; ring`
on the surviving summand branch. `simp` already closed the goal,
so `push_cast; ring` triggered "No goals to be solved". Fix: drop
the trailing `push_cast; ring` and let `simp` finish alone.

Same shape inside D.7's per-summand congruence: the strategy's
`simp [...]; push_cast; ring` left no goal after the `simp`.
Fix: drop the trailing `push_cast; ring`.

## Discovery
The `Polynomial.C ((-x : ℝ) : ℂ) * X^k` shape simplifies more
cleanly with `simp` alone (with the explicit Polynomial.eval_*
lemmas) than with the strategy's `simp; push_cast; ring` combo —
`simp` already pushes the negation through and closes the
arithmetic. Worth remembering for future ξ-evaluation closed-form
lemmas (D.9, D.10).

## Suggested next approach
* **D.9**: `D_mul_toGLM_charpoly_eval_one_concrete` — substitute
  `rowFBetaPoly_eval_one` (cycle 710 / D.5) and the new D.7 into
  the cycle 710 D.3 identity `D_mul_toGLM_charpoly_eval_one_eq`.
  Should be near-identical structure to D.8 (pure substitution + `ring`),
  modulo the extra `1 + ∑ α(castSucc l)` factor not being a single
  bare scalar.
* **D.10**: `rowFAlphaPoly_eval_zero` and `_eval_one`. Strategy
  flagged this as harder — `rowFAlphaPoly` routes through
  `Matrix.vecMul` against an adjugate at `X` (not at a scalar);
  needs `Matrix.adjugate_apply` + `Matrix.det_apply` expansion plus
  cycle 686 `natDegree` bounds for entry sparsity. Consider
  isolating helper lemmas first.
* **D.11**: degree-counting for spurious-root structure of general
  non-BDF LMMs — the substantive remaining milestone before the
  `LMM.toGLM_isAStable_iff` headline.
