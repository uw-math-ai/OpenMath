# Cycle 095 Results

## Worked on

* Closed sub-lemma B `GeneralLinearMethod.glmConstOneIterate_closed_form`
  in `OpenMath/Chapter5/Section514.lean` (the closed-form summation
  `y[n] = h • Σ_{k<n} V^k *ᵥ (B *ᵥ 𝟙)`).
* Documented the `u' = u` bridge gap as a new issue file
  `.prover-state/issues/u_prime_equals_u_bridge.md`.

## Approach

### Priority 0 — Aristotle one-shot check

Refreshed status of project `11f63aa0-7a38-45eb-a6c9-a86fff9b8149`.
Still `IN_PROGRESS` at 8 % after ~52 minutes — same as the cycle 094
checkpoint. Per CLAUDE.md "one check is enough", proceeded without
waiting and without resubmission.

### Priority 1 — Sub-lemma B (PRIMARY DELIVERABLE)

Standard induction on `n`, both cases as in the strategy sketch.

* **Base** (`n = 0`): `funext i; simp [GeneralLinearMethod.glmConstOneIterate]`
  closes immediately (empty sum, scalar mul of zero vector).
* **Inductive step**:
  1. Reshape RHS via `Finset.sum_range_succ'` (pulls out `k = 0` to
     the right).
  2. `simp_rw [pow_succ', ← Matrix.mulVec_mulVec]` rewrites the inner
     `V^(k+1) *ᵥ (B *ᵥ 𝟙)` to `V *ᵥ (V^k *ᵥ (B *ᵥ 𝟙))`.
  3. `rw [← Matrix.mulVec_sum]` factors `V *ᵥ` outside the sum.
  4. `pow_zero`, `Matrix.one_mulVec` collapses the trailing `V^0`
     term to `B *ᵥ 𝟙`.
  5. `smul_add` distributes the `h •`.
  6. `← Matrix.mulVec_smul` pushes `h •` through `V *ᵥ`.
  7. `← ih` substitutes the inductive hypothesis.
  8. After `funext i`, `show` reshapes the recurrence definitionally,
     then `simp only [Matrix.mulVec, dotProduct, ...]` + `add_comm` +
     `Finset.sum_congr` + `ring` finishes the per-component algebra.

Total: ~22 lines, well under the ~50 LOC budget. No private helpers
needed — the proof goes through linearly without decomposition.

### Priority 2 — Sub-lemma C (NOT ATTEMPTED)

Per the strategy's explicit warning ("Do NOT over-commit to C — better
to land B clean with C still open than to ship a broken C edit that
breaks B's compile"), and given the bridge `u' = u` is genuinely hard
(see issue file), I deliberately did not attempt sub-lemma C this
cycle. Cycle 094 was scored −2 for shipping broken work; cycle 095's
mandate is sorry-count regression, which sub-lemma B alone delivers
(3 → 2).

### Priority 3 — Bridge issue documentation

Wrote `.prover-state/issues/u_prime_equals_u_bridge.md` with:

* Precise statement of the bridge gap.
* What was tried (cycle 094 deferred; cycle 095 sketched the
  `V·u' = u'` half via continuity of `V *ᵥ ·`).
* Why it's hard (two failure modes: `U·u' = 𝟙` not extractable from
  the convergence statement; even `V·u' = u'` + `V·u = u` does not
  force `u' = u` without 1-eigenspace uniqueness).
* Three possible solutions (non-degeneracy hypothesis; smarter φ;
  preconsistency-uniqueness lemma).
* Cross-reference: this bridge plus sub-lemma D are the two remaining
  blockers for `thm:514A`.

### Priority 4 — Housekeeping

* `plan.md` and `lean_status.json` thm:514A row left at `[~]` —
  sub-lemma D + the bridge gap both remain, so the description is
  still accurate. Did not edit these files.
* Did not trim cycle-094 attempts.md note (out of scope; loop-internal).

## Result

**SUCCESS — sorry count 3 → 2.**

* `lake env lean OpenMath/Chapter5/Section514.lean` →
  `OpenMath/Chapter5/Section514.lean:148:8: warning: declaration uses sorry`
  (`cesaro_residual_tendsto_zero`),
  `OpenMath/Chapter5/Section514.lean:170:8: warning: declaration uses sorry`
  (`exists_inverse_of_cesaro_zero`).
  No errors. The closed-form theorem at line 96 is sorry-free.
* `lean_verify` of
  `OpenMath.Chapter5.Section510.GeneralLinearMethod.glmConstOneIterate_closed_form`
  → axioms `[propext, Classical.choice, Quot.sound]` only. No `sorryAx`.

This hits the strategy's **Minimum success bar** (3 → 2) cleanly.

## Faithfulness check

`glmConstOneIterate_closed_form` is a Lean-side helper (no entity ID),
not a textbook entity. It encodes the textbook formula

> `y^{[n]} = (1/n) [I + V + V² + ... + V^(n-1)] B·𝟙`

(Butcher §514, p. 410, the equation immediately after the `y^{[i]}`
recurrence) generalised from the textbook's `h = 1/n` to arbitrary
stepsize `h`. The Lean statement

```lean
M.glmConstOneIterate h n =
  h • (∑ k ∈ Finset.range n, (M.V ^ k) *ᵥ (M.B *ᵥ (fun _ => 1)))
```

is exactly this formula with `h • Σ` matching `(1/n) Σ` modulo
generalisation. **Lean statement captures: same content as the
textbook formula** (with the natural generalisation in `h`).

No new `def`, `class`, `structure`, or hypothesis was introduced.
The signature is unchanged from the cycle 094 scaffold; only the
proof body changed (sorry → tactic block).

## Dead ends

None — the planned proof skeleton went through on the first attempt
without backtracking. The only minor surprise was that the
componentwise reshape after the function-level rewrites needed
`add_comm` (because the recurrence puts `B`-term first but the
function-level RHS post-`smul_add` puts `V`-term first) and a
`Finset.sum_congr` + `ring` to commute `M.B i j * h` vs `h * M.B i j *
1`. Both are minor and expected.

## Discovery

* The five-step rewrite chain
  `Finset.sum_range_succ' → simp_rw [pow_succ', ← Matrix.mulVec_mulVec]
   → ← Matrix.mulVec_sum → smul_add → ← Matrix.mulVec_smul → ← ih`
  is a clean Mathlib-native pattern for "iterate-equals-Cesaro-sum"
  proofs. Worth remembering for any future iteration where the same
  structure appears (e.g. if §515/§516 introduce another GLM iterate
  in closed form).
* `Matrix.mulVec_smul` is `M.mulVec (b • v) = b • M.mulVec v`
  (scalar passes through `*ᵥ`); written backward it becomes the
  "pull `h •` outside `V *ᵥ`" rewrite. This combines naturally with
  `smul_add` for sum-of-mulVec terms.
* The function-level `rw` chain leaves a residual goal at the
  function level (`f = g`); a single `funext i` followed by the
  recurrence's definitional `show` exposes the per-component goal
  that simp + ring closes.

## Suggested next approach

For cycle 096 the planner has three candidate priorities:

1. **Tackle sub-lemma C with the partial bridge** — prove
   `V·u' = u'` as a private helper `convergence_witness_isVfixed`
   (the `V·u' = u'` half of the bridge from
   `u_prime_equals_u_bridge.md`). This requires:
   * Setting up the IsConvergent application machinery (φ ≡ 0,
     Y := M.glmConstOneIterate (1/n), the `Y n 0` and
     `IsGLMSolution` clauses).
   * Continuity of `V *ᵥ ·` on `Fin r → ℝ` (Mathlib has
     `Matrix.mulVec_continuous`-style results — verify locally).
   * Closed-form computation: `V *ᵥ Y n n - Y n n = (1/n) • (V^n - I) *ᵥ (B *ᵥ 𝟙)`
     and bound the RHS via `hPB` (`‖V^n‖ ≤ K`).
   This is non-trivial (~150 LOC estimated) but well-scoped and
   would set up the rest of sub-lemma C for a subsequent cycle.

2. **Attempt the preconsistency-uniqueness lemma** (option (c) in
   the bridge issue): prove "the preconsistency vector is unique up
   to scalar" as a §510 theorem, then use it to close the `u' = u`
   bridge in cycle 097. This is the most textbook-faithful path and
   may be cleaner than option (a) or (b).

3. **Defer §514 entirely and pivot to §515/§516** — if both bridge
   and sub-lemma D are multi-cycle blockers, working ahead in the
   chapter may unblock parallel progress while §514 awaits its
   infrastructure dependencies.

I'd recommend option 1 (the partial bridge): it makes documented
progress on §514 without speculation, ships a verifiable artifact
(a closed lemma), and leaves the strategic question of whether to
continue §514 vs pivot for the planner to weigh based on cycle 096
outcome.
