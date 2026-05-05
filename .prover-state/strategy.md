# Cycle 143 Strategy

## State summary

- **Sorry count**: 0 (all of Chapter 5 is sorry-clean as of cycle 142).
- **Recent score trend**: +1, +2, +2, +2 (cycles 139–142). Strong run.
- **Last cycle (142)**: closed `backwardEulerGLM_isLStable` — completing
  the 4-corner coverage matrix for `def:520F` (A-stable × L-stable,
  positive × negative). Axiom-clean.
- **No pending Aristotle results.** Cycle-141 Job A (thm:550A
  general-n) was cancelled at 6%; manual cofactor expansion is the
  only path forward, deferred per `thm_550A_general_n.md`.
- **Plan progress**: 69/175 entities (Chapter 5 is the active
  chapter, with 11/35 done).

## Cycle 143 target — Priority 1 (PRIMARY)

**Add an r=2 substantive L-stable witness `padded2DBackwardEulerGLM_isLStable`
to `def:520F`** in `OpenMath/Chapter5/Section520.lean`.

This mirrors the cycle 133/134 pattern that successfully strengthened
`def:551A` and `def:542A` non-vacuity from r=1 (vacuous/trivial) to
r=2 (substantive). Two successful precedents for this exact move
shape; both scored +2.

### Why this target

1. **Low risk, well-precedented**: Cycles 133 and 134 closed
   essentially the same problem shape (block-pad an r=1 GLM into r=2
   to discharge `i ≠ 0` clauses non-vacuously). Both axiom-clean,
   both scored +2.
2. **Reuses cycle-142 infrastructure**: `backwardEulerGLM_stabilityMatrix`
   is the load-bearing closed form, plus `padeZeroOne_norm_le_one_of_re_nonpos`
   and `norm_one_div_sub_tendsto_zero_cocompact` are already in scope.
3. **Strengthens a 4-corner-covered predicate**: `def:520F` already
   has positive trivial, positive substantive (`backwardEulerGLM`),
   and two negative witnesses. An r=2 substantive witness adds genuine
   non-vacuity strength beyond the r=1 case (matrix-power norm in r=2
   tests the block structure, not just scalar magnitude).
4. **Single-cycle scope**: estimated ~150 LOC, mostly mechanical
   block-padding + reuse of cycle-142 lemmas.

### Implementation outline

#### Step 0 — locate `padded2DEulerGLM` from cycles 133/134

**FIRST**: find the cycle-133 `padded2DEulerGLM` definition and
the cycle-133/134 witness theorems. They live in either
`OpenMath/Chapter5/Section510.lean` or `Section520.lean`. Use:

```
Grep pattern="padded2DEulerGLM" path=OpenMath/Chapter5/
```

Read the surrounding lines to learn:
- The exact file location (where to add the new GLM definition).
- The block-padding pattern (which entries are non-zero, where the
  `i = 0` block lives, what the `i = 1` rows/cols look like).
- The proof tactics used for the cycle 133/134 r=2 witnesses
  (these are the canonical templates).

Copy the padding pattern verbatim; only the underlying r=1 block
changes (backward Euler vs. explicit Euler).

#### Step 1 — define `padded2DBackwardEulerGLM`

Place next to `padded2DEulerGLM`. Use the cycle-133 padding scheme,
substituting backward-Euler tableau entries (`A = U = B = V = !![1]`
in the r=1 block, padded with zeros). Concretely the scheme will
look like

```lean
noncomputable def padded2DBackwardEulerGLM : GeneralLinearMethod 2 2 :=
  { A := !![1, 0; 0, 0]
    U := !![1, 0; 0, 0]    -- match cycle-133's U-padding pattern
    B := !![1, 0; 0, 0]
    V := !![1, 0; 0, 0] }
```

but **read cycle 133's padding to confirm the U/V padding scheme**;
do not invent it freshly.

#### Step 2 — closed-form stability matrix

```lean
theorem padded2DBackwardEulerGLM_stabilityMatrix (z : ℂ) (hne : z ≠ 1) :
    padded2DBackwardEulerGLM.stabilityMatrix z = !![1/(1-z), 0; 0, 0]
```

Proof strategy: `(I − zA) = !![1−z, 0; 0, 1]` is invertible iff
`z ≠ 1`. Inverse is `!![1/(1−z), 0; 0, 1]`. Multiply through:
`V + zB(I−zA)⁻¹U = 0 + z·!![1,0;0,0]·!![1/(1−z),0;0,1]·!![1,0;0,0]
= !![z/(1-z), 0; 0, 0]`. Then `1 + z/(1-z) = 1/(1-z)` gives the
result.

If `Matrix.inv_subsingleton` doesn't fit (it's `Subsingleton`-based
and may only fire on 1×1), use the explicit 2×2 inverse formula
via `Matrix.det_fin_two` and `Matrix.adjugate` or compute by
showing `M * !![1/(1-z), 0; 0, 1] = 1` via `Matrix.ext` + `fin_cases`.

#### Step 3 — A-stability witness `padded2DBackwardEulerGLM_isAStable`

The matrix-power `M(z)^k` for `M(z) = !![a, 0; 0, 0]` (with `a := 1/(1-z)`):
- `k = 0`: identity matrix.
- `k ≥ 1`: `!![a^k, 0; 0, 0]` (computable by induction on `k`, or
  by `Matrix.mul_fin_two`).

For the L∞ operator norm (the default in `M.IsStable`/`IsAStable`
scope), `‖!![a^k, 0; 0, 0]‖_∞ = ‖a^k‖ = ‖a‖^k ≤ 1` by cycle 142's
`padeZeroOne_norm_le_one_of_re_nonpos`.

For `k = 0`, `‖I‖_∞ = 1`. So the witness `C := 1` works for all `k`.

**Verify the matrix norm scope** in Section520 first (search for
`open scoped Matrix.Norms`). Cycle 142's `backwardEulerGLM_isAStable`
shows the canonical pattern; copy it.

Sub-helper (private) needed:

```lean
private lemma fin_two_pow_diag_with_zero (a : ℂ) (k : ℕ) :
    (!![a, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)^k =
      if k = 0 then 1 else !![a^k, 0; 0, 0]
```

Proof by induction on `k`, using `Matrix.mul_fin_two` for the step
case.

#### Step 4 — L-stability witness `padded2DBackwardEulerGLM_isLStable`

Combine Step 3 with the cocompact spectral-radius limit. The
spectral radius of `!![a, 0; 0, 0]` equals `‖a‖₊` (eigenvalues are
`a` and `0`). Apply cycle 142's `norm_one_div_sub_tendsto_zero_cocompact`
to push `ρ(M(z)) → 0` along `cocompact ℂ`.

Sub-helper (private) needed:

```lean
private lemma spectralRadius_diag_2_with_zero (a : ℂ) :
    spectralRadius ℂ (!![a, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) = ↑‖a‖₊
```

Proof routes:
1. Direct: spectrum of `!![a, 0; 0, 0]` is `{0, a}` (compute via
   `Matrix.det_fin_two` characteristic polynomial). Spectral
   radius is `max ‖0‖ ‖a‖ = ‖a‖`.
2. Or: copy cycle 137's `spectralRadius_fin_one` proof technique
   and adapt for the diagonal-2 case.

Choose route 1 if Mathlib's `Matrix.charpoly` API on `Fin 2` is
clean; route 2 if not.

### Verification gates (all must pass)

- `lake env lean OpenMath/Chapter5/Section520.lean` clean.
- `lake env lean OpenMath/Chapter5/Section510.lean` clean (if you
  edit it to add the GLM definition).
- `lake build OpenMath.Chapter5` clean.
- `mcp__lean-lsp__lean_verify` on `padded2DBackwardEulerGLM_isLStable`
  AND `padded2DBackwardEulerGLM_isAStable` returns axioms
  `[propext, Classical.choice, Quot.sound]` ONLY. **No `sorryAx`.**
- `grep -rn '\bsorry\b' --include='*.lean' OpenMath/`: no actual
  `sorry` in proof bodies (doc-comment refs OK).
- Tautology scanner: 0 hits on the new declarations.

## What NOT to try

1. **Do NOT touch `thm:550A` general-n.** Cycle 141 confirmed
   Aristotle cannot do it (cancelled at 6% after 24h); cycles 138–140
   already delivered n=1 and n=2 stepping stones. The general-n
   manual proof needs cofactor-expansion induction infrastructure
   that is multi-cycle work; **out of scope** for cycle 143.
2. **Do NOT open `def:442A` (principal sheet).** Riemann surface +
   local injectivity infrastructure is multi-cycle work. Cycle 142's
   strategy explicitly overruled this option for the same reason.
3. **Do NOT open `def:530B` or `def:530C`.** Per cycle 142 strategy,
   the `applyStartingMethod`/`applyGLMStep` infrastructure (~250 LOC)
   is too expensive for a single cycle and risks faithfulness
   divergence. Save for a dedicated infra cycle.
4. **Do NOT raise `maxHeartbeats`** above 200000. Decompose if
   needed.
5. **Do NOT introduce `axiom` or `constant`.** No exceptions.
6. **Do NOT submit to Aristotle this cycle.** Problem is small enough
   that manual is faster, and there are no pending submissions.
   Cycle 142 succeeded without Aristotle on the same problem shape.
7. **Do NOT rely on `Matrix.inv_subsingleton` for the 2×2 case.**
   It's `Subsingleton`-based and is for 1×1 matrices only. Use the
   explicit 2×2 inverse formula via direct computation.
8. **Do NOT redefine `IsAStable` or `IsLStable`.** They were
   stabilised in cycles 088/137; reuse them directly.
9. **Do NOT silently change the matrix norm scope.** Section520 has
   a default norm scope (check for `open scoped Matrix.Norms.…`); if
   the L-stability witness needs an operator-norm bound that
   conflicts with the default, do it in a sub-section that opens
   the alternate scope (cycle 124's pattern in Section515).
10. **Do NOT invent a fresh padding pattern.** Read cycle 133/134's
    `padded2DEulerGLM` and copy its block-padding scheme verbatim,
    only swapping the r=1 block content.

## Backup plan — if the r=2 backward-Euler witness stalls

If matrix power computation gets stuck (e.g., `Matrix.mul_fin_two`
case analysis blows up) or if the spectral-radius helper proves
unexpectedly hard, fall back in this order:

### Backup A (preferred fallback): `thm:550A` n=3 stepping stone

Add `doublyCompanionMatrix_det_factorization_n_three` axiom-clean
via `Matrix.det_fin_three`. Same pattern as cycle 138 (n=1) and
cycle 140 (n=2). The residue's leading coefficients should follow
the pattern `-(α_i · β_{n-i})` summed over `i = 0..n-1` (visible at
n=1, n=2; the n=3 case will give a third data point for the eventual
general-n proof). Estimated ~80 LOC. Axiom-clean win.

### Backup B (if A also stalls): degenerate-pair witness expansion for §530

Cycle 141 added `mixedStartingMethod` (heterogeneous stages r=2)
for `def:530A`. A natural follow-up: a *third* witness exercising
a different degeneracy axis — e.g. `r=3` with stages `(1, 1, 2)` or
`(1, 2, 1)` — to further strengthen the non-vacuity story. Pattern
mirrors cycle 141 verbatim. ~100 LOC.

### Backup C (last resort): documentation cycle

If all proof work blocks, write or update `.prover-state/issues/`
files documenting the failure mode discovered. Ensure at minimum
one issue file is touched so the cycle has a non-zero diff (per
CLAUDE.md "A cycle with zero changes is unacceptable"). Score will
be 0 or low-positive at best, but avoids regression.

## Pre-commit checklist (mandatory)

For every new `def`, `theorem`, `lemma`:

- [ ] Tautology check: no proof body is `exact <hypothesis>` of the
      conclusion's literal shape.
- [ ] Identity check: no theorem is a single-`exact` re-export.
- [ ] Hypothesis strength check: every hypothesis is necessary
      (especially `z ≠ 1` if you reuse cycle-142's bridge).
- [ ] Faithfulness: `padded2DBackwardEulerGLM` is a *named instance*,
      not a new mathematical concept — no `entities/<id>.json` lookup
      needed (matches cycle 133/134 precedent).
- [ ] `#print axioms` on the public theorems shows only
      `[propext, Classical.choice, Quot.sound]`.
- [ ] No private helper has unused hypotheses (Lean's linter will
      catch `_`-prefixed or genuinely unused — do a final pass).

## Task results to write

`.prover-state/task_results/cycle_143.md`, including:
- Worked on
- Approach (specific lemmas + tactics used; cite which cycle-133/134
  pattern was reused)
- Result (SUCCESS / PARTIAL / FAILED)
- Faithfulness check (per new theorem)
- Dead ends
- Discovery (especially: matrix-norm scope confirmation, padding
  pattern observations)
- Suggested next approach for cycle 144
