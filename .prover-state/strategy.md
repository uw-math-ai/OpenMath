# Strategy — Cycle 84

## TOP PRIORITY: Fix CLAUDE.md heartbeat violation in `OpenMath/SpectralBound.lean`

Cycle 83 integrated an Aristotle-generated proof but **left two `set_option maxHeartbeats` overrides above 200000**, in direct violation of CLAUDE.md's hard rule:

> **Never increase `maxHeartbeats` above 200000. Decompose the proof instead.**

This is the highest-priority issue in the project. It blocks every future cycle (the bar is "no committed file may exceed the heartbeat limit"). The Dahlquist barrier sorrys in `MultistepMethods.lean` (lines 1241, 1258) have **16+ failed attempts** and remain off-limits this cycle.

Issue file: `.prover-state/issues/spectral_bound_heartbeat_decomposition.md`.

## Sorry inventory (snapshot)

| # | File | Line | Theorem | Status |
|---|------|------|---------|--------|
| 1 | MultistepMethods.lean | 1241 | `hasDerivAt_Gtilde_one` | **DO NOT TOUCH** (16+ failed cycles) |
| 2 | MultistepMethods.lean | 1258 | `continuousOn_Gtilde_closedBall` | **DO NOT TOUCH** (16+ failed cycles) |

`SpectralBound.lean` and `DahlquistEquivalence.lean` currently have **0 sorrys**, but `SpectralBound.lean` has **2 forbidden `set_option maxHeartbeats` lines** that count as the moral equivalent of an open issue.

## PHASE 0: Aristotle check (≤ 5 min)

No Aristotle jobs are pending from cycle 83. Do **not** submit new jobs this cycle — this is a refactoring/decomposition task that is best done by hand because it requires precise extraction of intermediate lemmas. Aristotle would just regenerate another monolithic proof.

If for any reason you discover an outstanding Aristotle job from prior cycles that closes a sorry, incorporate it first, then return to the heartbeat task.

## PHASE 1: Map the two hot proofs

Re-read `OpenMath/SpectralBound.lean` (it is large; use `Read` with no offset to get the whole file). The two violations are:

1. **Line 70**: `set_option maxHeartbeats 800000 in` before `pow_apply_eq_sum_of_genEigenspace` (~lines 71–195). Hot block is the induction step around lines 80–93 with heavy `simp +decide` calls.
2. **Line 201**: `set_option maxHeartbeats 1600000 in` before `uniformly_bounded_iterates_of_spectral_bound` (~lines 202–283). Hot block is `h_bound_basis` and the `choose` block at lines 213–258.

Confirm these line numbers with `Read` before editing — cycle 83 may have shifted them slightly.

## PHASE 2: Decompose `pow_apply_eq_sum_of_genEigenspace`

Extract these helper lemmas **above** the main theorem so each one compiles within the default 200000 heartbeats:

### A1. `tupleSucc_apply_finsum_genEigenspace_step`
Pull out the inner per-step computation: applying `T^(n+1)` to a finite sum over generalized eigenspaces, in terms of `T^n`. This is the line that currently forces `simp +decide` to chew through every eigenspace simultaneously.

### A2. `pascal_recombination_genEigenspace`
Pull out the Pascal-triangle / binomial recombination identity that the proof uses to re-fold `(n+1) choose k = n choose k + n choose (k-1)`. Prove it as a standalone `lemma` over `ℕ`, then apply it inside the main theorem.

### A3. `genEigenspace_succ_index`
Pull out the algebraic step that re-indexes the sum from `Finset.range (n+1)` to `Finset.range n` plus a boundary term. State it as a clean equality between two `Finset.sum`s, prove by `Finset.sum_range_succ` + ring.

After extraction, the body of `pow_apply_eq_sum_of_genEigenspace` should be a short induction whose step calls `A1`, then `A2`, then `A3`. Verify with:

```bash
lake env lean OpenMath/SpectralBound.lean
```

**Then delete `set_option maxHeartbeats 800000 in` (line 70).** If the proof still times out, decompose further — do **not** put the option back.

## PHASE 3: Decompose `uniformly_bounded_iterates_of_spectral_bound`

Extract these helper lemmas **above** the main theorem:

### B1. `bound_on_one_genEigenspace_component`
For a single μ with `‖μ‖ ≤ 1`, give `∃ C, ∀ n, ∀ v ∈ maxGenEigenspace T μ, ‖T^n v‖ ≤ C * ‖v‖`. This is the per-eigenspace bound that the main proof currently inlines via `choose`.

### B2. `bound_on_basis_vector`
Combine B1 across the finite set of basis vectors of the eigendecomposition: for each basis vector `e_i`, give a constant `C_i` such that `∀ n, ‖T^n e_i‖ ≤ C_i`. State as `∃ C : ι → ℝ, ...`.

### B3. `linear_map_to_basis_repr_continuous`
The fact that decomposing a vector along a finite basis is a bounded linear operation, so `‖coords v‖ ≤ K * ‖v‖` for some `K`. In `FiniteDimensional` this is automatic; encapsulate it as a single helper lemma so the main proof can use it as one term.

After extraction, the body of `uniformly_bounded_iterates_of_spectral_bound` should be: `B1` → `B2` (via `Finset.choose` or pointwise pick) → triangle inequality + `B3`. Verify with:

```bash
lake env lean OpenMath/SpectralBound.lean
```

**Then delete `set_option maxHeartbeats 1600000 in` (line 201).** If still timing out, decompose further.

## PHASE 4: Verify downstream

```bash
lake env lean OpenMath/SpectralBound.lean
lake env lean OpenMath/DahlquistEquivalence.lean
lake env lean OpenMath/MultistepMethods.lean
```

`DahlquistEquivalence.lean` imports `SpectralBound` and uses `uniformly_bounded_iterates_of_spectral_bound`. If the decomposition changes the lemma signature, update the call site there.

## What NOT to try

- **Do NOT bump `maxHeartbeats` higher.** This is the entire point of the cycle.
- **Do NOT silently lower it** to e.g. 400000 and call it a win. The CLAUDE.md cap is 200000. Anything above is a violation.
- **Do NOT rewrite either proof from scratch** — the Aristotle proof is correct, it just needs to be sliced into compile-able pieces. Preserve the proof structure; only extract sub-blocks.
- **Do NOT submit either proof to Aristotle.** Aristotle generates monolithic proofs; that's how we got into this mess. Decomposition is structural editing, not search.
- **Do NOT touch `MultistepMethods.lean` lines 1241 or 1258.** Those are the Dahlquist barrier sorrys. Cycles 1–78 have already documented dead ends; revisiting them this cycle would burn the whole cycle on a known-hard problem while leaving the heartbeat regression in place.
- **Do NOT add a new `import` to SpectralBound.lean** that brings in heavy Mathlib files. The decomposition should use only the imports already present.
- **Do NOT remove the existing helper lemmas** (`exists_bound_poly_geom`, `exists_bound_binom_geom`, `norm_pow_le_on_maxGenEigenspace`, `charPoly_ne_zero`, `rootMultiplicity_eq_one_of_root_deriv_ne_zero`, `maxGenEigenspace_le_one_of_charPoly_simple`). They are dependencies of the main theorems.

## Sorry-first protocol

For each helper lemma A1, A2, A3, B1, B2, B3:

1. State the lemma signature with `:= by sorry`.
2. Verify the file compiles with all helpers as sorry.
3. Refactor the main theorem to call the sorry helpers; verify it compiles within 200000 heartbeats. If it still doesn't, either the decomposition is too coarse (extract more) or you mis-identified the hot block.
4. Once decomposition compiles, close the sorrys one by one by lifting code out of the original proof body.

## Acceptance criteria

- [ ] Zero `set_option maxHeartbeats` lines remain in `OpenMath/SpectralBound.lean` (grep to confirm).
- [ ] `lake env lean OpenMath/SpectralBound.lean` succeeds with no warnings about heartbeats.
- [ ] `lake env lean OpenMath/DahlquistEquivalence.lean` succeeds.
- [ ] `lake env lean OpenMath/MultistepMethods.lean` succeeds.
- [ ] Total project sorry count is unchanged (still 2, both in MultistepMethods.lean).
- [ ] `.prover-state/task_results/cycle_084.md` written.
- [ ] `.prover-state/issues/spectral_bound_heartbeat_decomposition.md` deleted (or marked resolved).
- [ ] Commit and push.

## Fallback plan if blocked

If after extracting A1–A3 / B1–B3 the proofs still won't compile under 200000:

1. **Do not** restore the `set_option`. That is not a fallback.
2. Extract a second tier of sub-lemmas from the helpers themselves (e.g. break A2's Pascal identity into two arithmetic facts).
3. If genuinely stuck after multiple decomposition attempts, write a detailed `.prover-state/issues/spectral_bound_decomposition_attempt_84.md` explaining:
   - The decomposition tried (A1–A3 / B1–B3 contents).
   - Which helper still exceeds 200000 heartbeats and the specific tactic block responsible.
   - The next decomposition you would try in cycle 85.
4. Commit the partial decomposition with sorrys for the still-too-heavy pieces, **but only if** removing the `set_option` keeps the file compiling (sorrys are allowed; oversized heartbeats are not).

## Rules reminder

- Sorry-first: write full structure with sorry, verify compilation, then close.
- Do NOT increase maxHeartbeats above 200000 (this is the whole task).
- A cycle with zero changes is UNACCEPTABLE.
- Prefer `lake env lean OpenMath/<File>.lean` over `lake build`.
- After all checks pass, commit and push.
