# Cycle 404 Results

## Worked on

Closed-form exponential bound on the geometric-sum factor returned by
`discrete_gronwall_geometric`. Added three new lemmas to
`OpenMath/LMMTruncationOp.lean` immediately after
`discrete_gronwall_geometric`:

- `LMM.pow_one_add_le_exp_mul`: `(1 + a)^n ≤ exp(a · n)` for `0 ≤ a`.
- `LMM.geom_sum_le_nat_mul_exp_mul`:
  `∑_{k<n} (1 + a)^k ≤ n · exp(a · n)` for `0 ≤ a`.
- `LMM.discrete_gronwall_exp`: closed-form exponential discrete Grönwall
  `e n ≤ exp(a·n) · e 0 + n · exp(a·n) · b`.

## Approach

Followed the planner's Step 1–4 template directly. No detour, no
freelancing.

## Aristotle bundles triage

Inspected the bundle list summarized in the planner harness:

- `cce2b582` (`PowOneAddNonneg.lean`): cycle-403 territory, already live.
- `d218a207` (`DiscreteGronwallZeroInitial.lean`): cycle-403 zero-initial
  variant, already trivially derivable from the live geometric form.
- `c0eab6ac` (`DiscreteGronwallStep.lean`): cycle-403 inductive-step
  reshaper, already absorbed.
- `1c0756be` (`DiscreteGronwallHeadline.lean`): cycle-403 headline,
  already live as `discrete_gronwall_geometric`.
- `2848da47` (`GeometricSumSucc.lean`, COMPLETE_WITH_ERRORS):
  cycle-403 successor identity, already absorbed inline in the live
  `discrete_gronwall_geometric` proof; partial result not transplanted.
- `ce03c532`, `5a8bb9d7`, `a788200c`, `957b606a`: full two-file
  replacements of `LMMTruncationOp.lean` and `MultistepMethods.lean`.
  **Rejected wholesale** per planner mandate — these would rebuild the
  live `LMM` / `truncationOp` / `errorConstant` interface and risk
  re-introducing sorries. None of the bodies inside provided
  recoverable single-lemma proofs targeting the cycle 404 work, so no
  fragments were lifted.

No new Aristotle jobs were submitted this cycle: the planner-described
work is small enough (~50 lines of Lean) that the manual proof was
written and verified inside the file in one pass, and the cycle-403
bundle backlog already exhausts the recently-batched jobs targeting
this thread. Submitting another batch only to wait 30 minutes would
delay the deliverable without improving it.

## Result

SUCCESS.

- File compiles clean with
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMTruncationOp.lean`.
- `lean_verify LMM.discrete_gronwall_exp` reports axioms
  `[propext, Classical.choice, Quot.sound]` — standard only.
- Fallback (quadratic bound) was **not** needed.
- Mathlib lemmas used:
  - `Real.add_one_le_exp` (single-step exponential bound).
  - `Real.exp_nat_mul` to rewrite `(exp a)^n = exp (a · n)`.
  - `Real.exp_le_exp` to compare `exp(a·k)` and `exp(a·n)` via
    monotonicity.
  - `pow_le_pow_left₀` for the lifted power inequality.
  - `Finset.sum_le_sum`, `Finset.sum_const`, `Finset.card_range` for
    the geometric-sum bound.
  - `mul_le_mul_of_nonneg_left/right`, `add_le_add`, `linarith`,
    `ring` for assembly.

## Dead ends

None this cycle. The `Real.add_one_le_exp` and `Real.exp_nat_mul`
shapes were stable in Mathlib, so the fallback path was unnecessary.

## Discovery

`Real.exp_nat_mul a n` rewrites `Real.exp (n * a) = Real.exp a ^ n`
(left-to-right form). To get the multiplication-by-`a` form
`Real.exp (a * n)` cleanly, the rewrite combined with `ring_nf` to
absorb the order swap. This pattern will be reusable for the LMM
global-error theorem, where `a = h · L`.

## Suggested next approach

Cycle 405 should now assemble the **LMM global-error theorem**:
combine the one-step Lipschitz forcing recurrence with
`discrete_gronwall_exp`, with `a := h · L`, `b := C · h^(p+1)`,
and the bound `n · h ≤ T` to extract the textbook `O(h^p)` global
error. The likely sub-theorem missing is a one-step error recurrence
of the form

```lean
‖e (n+1)‖ ≤ (1 + h · L) * ‖e n‖ + C · h^(p+1)
```

derived from local truncation plus a Lipschitz bound on the right-hand
side. If proving that exposes a Picard–Lindelöf / Lipschitz seam not
yet in the codebase, decompose it as the first cycle 405 task and
write the global error theorem on top after the seam is built.
