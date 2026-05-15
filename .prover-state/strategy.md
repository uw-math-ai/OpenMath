# Cycle 298 Strategy — (342g) Aristotle poll + branch-dispatch

## Context

`lem:342A` is **partial**: properties (342a)–(342f) are all formalized
(cycles 271–293); only (342g) — `P_n^*` has `n` distinct real zeros in
`(0, 1)` — remains. Empirical anchors are shipped for `n ∈ {1, 2, 3, 5, 7}`
(cycles 294–297, all axiom-clean).

Aristotle project `5939f28b-c890-4b7f-be4f-ed0f31f0d0b5` was submitted
cycle 294 for the general (342g) statement. Most recent poll (cycle 297,
2026-05-15T23:19:53Z): `IN_PROGRESS`, `percent_complete = 25`. This is
**observation #1** of the three-stall protocol (cycle 285 precedent
established by `c8b8f138` / `efe4940e`).

Three-stall protocol (recap):
- Stall obs #1: poll, observe flat at X%, DO NOT cancel. Branch B (ship
  anchor).
- Stall obs #2: poll, observe still flat at X%, DO NOT cancel. Branch B.
- Stall obs #3: poll, observe still flat at X% → **cancel**, pivot to
  manual closure plan from `lem_342A_g_zeros_scoping.md` Branch D.

Current sorry count: 0. No active blockers; no infrastructure work
required. Cycle 298 is a continuation of the (342g) closure track.

## Priority 1 (P1) — Single-poll Aristotle `5939f28b`

**Command**: invoke `mcp__aristotle__get_status` with project_id
`5939f28b-c890-4b7f-be4f-ed0f31f0d0b5`. **One poll only.** Do NOT
re-poll under any circumstances per CLAUDE.md and the cycle 282–286
precedent.

### Branch dispatch table

After the single poll, dispatch on `status` and `percent_complete`:

| Status | percent_complete | Action |
|---|---|---|
| `COMPLETE` | 100 | **Branch A** — integrate, see §A below |
| `IN_PROGRESS` | < 25 | Branch B + flag regression for cycle 299 |
| `IN_PROGRESS` | 25 (same as cycle 297) | **Branch B** — observation #2, ship n=9 anchor |
| `IN_PROGRESS` | > 25 (healthy progress) | Branch B — ship n=9 anchor, stall counter resets |
| `COMPLETE_WITH_ERRORS` | — | **Branch C** — review errors, see §C below |
| `FAILED` / `CANCELLED` / `ERROR` | — | **Branch D** — escalate to manual plan |

**Most likely outcome**: IN_PROGRESS at 25% (observation #2). Per cycle
296→297 pace, +0pp/cycle has been the steady state since cycle 296.
Plan around Branch B.

## Priority 2 (P2) — Branch B (most likely): ship `butcherShiftedLegendre_nine_roots`

### Deliverable

Mechanical extension of the cycle 297 `n = 7` recipe to `n = 9`. Reuse:

- `butcherShiftedLegendre_nine` (cycle 285, `Section342.lean`):
  closed form
  `P_9^* = 48620X^9 − 218790X^8 + 411840X^7 − 420420X^6
   + 252252X^5 − 90090X^4 + 18480X^3 − 1980X^2 + 90X − 1`
- `butcherShiftedLegendre_eval_half_eq_zero_of_odd` (cycle 295):
  middle root `r_5 = 1/2` via `Odd 9` witnessed by `9 = 2·4 + 1`,
  i.e. `⟨4, rfl⟩`.
- `Polynomial.continuous` + `intermediate_value_Ioo` /
  `intermediate_value_Ioo'`: same IVT machinery as cycles 295/296/297.

### Bracket plan (9 roots in (0,1))

Approximate root locations (Gauss-Legendre nodes on [0,1] for n=9):
≈ {0.0159, 0.0820, 0.1934, 0.3378, 0.5, 0.6622, 0.8066, 0.9180, 0.9841}.

Choose disjoint brackets with small denominators. Suggested:

| Root | Bracket | Direction | Strategy |
|---|---|---|---|
| r₁ ≈ 0.016 | (0, 1/20) | ascending | `f(0) = -1`, `f(1/20) > 0` |
| r₂ ≈ 0.082 | (1/20, 1/8) | descending | `f(1/20) > 0`, `f(1/8) < 0` |
| r₃ ≈ 0.193 | (1/8, 1/4) | ascending | `f(1/8) < 0`, `f(1/4) > 0` |
| r₄ ≈ 0.338 | (1/4, 2/5) | descending | `f(1/4) > 0`, `f(2/5) < 0` |
| r₅ = 1/2 | — | parity helper | `f(1/2) = 0` exact |
| r₆ ≈ 0.662 | (3/5, 3/4) | ascending | parity-symmetric to r₄ |
| r₇ ≈ 0.807 | (3/4, 7/8) | descending | parity-symmetric to r₃ |
| r₈ ≈ 0.918 | (7/8, 19/20) | ascending | parity-symmetric to r₂ |
| r₉ ≈ 0.984 | (19/20, 1) | descending | parity-symmetric to r₁ |

**Sanity-check brackets before committing**: compute each
`P_9^*(endpoint)` using exact rational arithmetic (Python `Fraction`
or hand-evaluation). Worker should verify each sign is as table claims;
if any sign mismatches, **adjust the bracket** before writing Lean.
Likely-tight brackets at the outer roots r₁ and r₉ — denominator 20 may
be too coarse; try 1/50 or 1/100 if 1/20 doesn't give correct sign.

**Backup bracket strategy** (if 1/20 fails): use denominators ≤ 100
(e.g. 1/100, 9/50, …). The denominator size only affects `norm_num`
load, not soundness. Cycle 296/297 used denominators ≤ 10/20; n=9 may
need ≤ 100.

### Recipe (per cycle 296/297 template)

For each bracket `(a, b)`:
1. Evaluate `P_9^*(a)` and `P_9^*(b)` via:
   ```lean
   have hfa : (butcherShiftedLegendre 9).eval a = <value> := by
     rw [butcherShiftedLegendre_nine]
     simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
           Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
     norm_num
   ```
2. Apply `intermediate_value_Ioo` (ascending) or `intermediate_value_Ioo'`
   (descending) with `Polynomial.continuous _ |>.continuousOn` and the
   appropriate `Set.mem_Ioo` witness for `0 ∈ Ioo (f a) (f b)`.
3. Extract `r ∈ Ioo a b` with `(butcherShiftedLegendre 9).eval r = 0`.

For the middle root r₅:
```lean
have hf5 : (butcherShiftedLegendre 9).eval (1/2 : ℝ) = 0 :=
  butcherShiftedLegendre_eval_half_eq_zero_of_odd 9 ⟨4, rfl⟩
```

Membership in `(0, 1)`: each `r_i ∈ Ioo a b ⊆ Ioo 0 1` via
`Set.Ioo_subset_Ioo` (need `0 ≤ a` and `b ≤ 1`).

Distinctness (36 pairs for 9 roots): use disjoint intervals + `linarith`
in a chain:
```
(0, 1/20) < (1/20, 1/8) < (1/8, 1/4) < (1/4, 2/5)
  < {1/2} < (3/5, 3/4) < (3/4, 7/8) < (7/8, 19/20) < (19/20, 1)
```
Each consecutive pair has the closing endpoint ≤ the next opening
endpoint. `1/2` is strictly between `2/5` and `3/5`.

### Statement skeleton

```lean
/-- (342g) at n = 9: `P_9^*` has 9 distinct real zeros in (0, 1). -/
theorem butcherShiftedLegendre_nine_roots :
    ∃ r₁ r₂ r₃ r₄ r₅ r₆ r₇ r₈ r₉ : ℝ,
      r₁ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₂ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₃ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₄ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₅ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₆ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₇ ∈ Set.Ioo (0 : ℝ) 1 ∧ r₈ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₉ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ … ∧ r₈ ≠ r₉ ∧  -- 36 distinctness conjuncts
      (butcherShiftedLegendre 9).eval r₁ = 0 ∧
      (butcherShiftedLegendre 9).eval r₂ = 0 ∧ … ∧
      (butcherShiftedLegendre 9).eval r₉ = 0 := by
  -- ~340 LOC, mechanical port of cycle 297's n=7 proof
```

**LOC estimate**: ~340 (one more bracket pair than n=7's 274 LOC plus
the parity-symmetric tail). Hard ceiling 400 LOC; if blowing past,
factor evaluations into private helpers.

### Risks and mitigations (P2)

| Risk | Mitigation |
|---|---|
| Bracket sign mismatch | Pre-compute every endpoint with Python `Fraction`; verify before writing |
| `norm_num` slow at n=9 (9-digit coefficients) | If a single evaluation > 60s wall, split coefficients into `have`-binds |
| Heartbeat ceiling on the full proof | Factor each bracket pair into a `private theorem`, then assemble. **Do NOT raise maxHeartbeats** |
| Distinctness `linarith` chain blowing up | Pre-establish bracket endpoints as named `have`s; use `linarith [h₁, h₂, …]` with explicit list |

### Faithfulness check (P2)

- **Entity ID**: `lem:342A` clause (342g) at n = 9.
- **Textbook**: clause (342g) is a ∀-claim; this is an empirical anchor
  (strictly weaker). Do NOT bump `lean_status.json` row for `lem:342A`
  to `formalized`. State remains `partial` until Aristotle (or manual
  closure) lands the general statement.
- **Definition smuggling check**: no new definitions. Only one new
  theorem `butcherShiftedLegendre_nine_roots`.
- **Hypothesis strength**: zero hypotheses (a closed theorem about a
  concrete polynomial).

## Priority 3 (P3) — Branch A (if Aristotle COMPLETE)

### Integration recipe

1. Download Aristotle artifact:
   ```
   mcp__aristotle__download_result project_id=5939f28b…
   mcp__aristotle__extract_result project_id=5939f28b…
   ```
2. Inspect `ARISTOTLE_SUMMARY.md` and the generated Lean file(s) in
   `.prover-state/aristotle_results/5939f28b-c890-4b7f-be4f-ed0f31f0d0b5/`.
3. Identify the main theorem (probably named
   `butcherShiftedLegendre_distinct_zeros` or
   `butcherShiftedLegendre_has_n_distinct_real_zeros`).
4. Identify all helper lemmas (sign-change extraction, product-polynomial
   construction, integral-positivity, orthogonality-contradiction).
5. **Decide placement**:
   - If helpers are reusable (sign-change machinery is general), place
     in a new file `OpenMath/Chapter3/Section342ZerosHelpers.lean`
     (mirroring cycle 281's `Section342NormSqHelpers.lean` pattern).
   - If helpers are tightly coupled to the main theorem, inline them
     into `Section342.lean` as `private` lemmas.
6. Integrate the main theorem into `Section342.lean` at the end of the
   namespace (after the empirical anchors).
7. **Audit imports**: Aristotle uses cycles 271–293 results
   (`butcherShiftedLegendre_orthogonal`, `_orthogonal_to_lower_degree`,
   `_recurrence`, `_natDegree`, `_leadingCoeff`, `_zero`/`_one`/…/`_eleven`).
   Verify each is cited at HEAD; rename if Aristotle used a stub name.
8. Compile: `lake env lean OpenMath/Chapter3/Section342.lean` (or
   `Section342ZerosHelpers.lean` first). Must close clean.
9. Verify axiom-clean: `#print axioms <main_theorem>` returns
   `[propext, Classical.choice, Quot.sound]` only.
10. **Update entity status** (only if integration succeeds):
    - `extraction/formalization_data/lean_status.json` row for
      `lem:342A`: status `partial` → `formalized`, `lean_symbol` set
      to the main theorem name, `cycle_closed` set to 298.
    - `plan.md` Chapter 3 row for `lem:342A`: `[~]` → `[x]`, update
      the inline note.
11. Update `MEMORY.md` if any new Lean idiom or Mathlib lemma is
    introduced by Aristotle.

### Branch A risks

| Risk | Mitigation |
|---|---|
| Aristotle uses a stub helper name not at HEAD | Rename to the correct project symbol (e.g. `M.foo` → `LinearMultistepMethod.foo M`) |
| Aristotle's proof has tactic errors | Run `lake env lean` to surface, fix the first error (often namespace), retry |
| Aristotle's helpers conflict with existing private symbols | Rename Aristotle's symbols with a `private` prefix or move to the helpers file |
| Main theorem statement diverges from textbook | If Aristotle proves a weaker / stronger statement, document the divergence; consider re-submitting if strictly weaker |

## Priority 4 (P4) — Branch C (if COMPLETE_WITH_ERRORS)

Mirror the cycle 184 protocol for `7c4d0ffb` (Phase C.2 of `lem:441A`):
1. Read `ARISTOTLE_SUMMARY.md` for the error description.
2. Diff Aristotle's generated file against the submission file.
3. If errors are ≤ 3 syntactic issues (namespace, simp set, name drift):
   apply fixes locally, run `lake env lean`, integrate.
4. If errors are deeper (wrong proof strategy, missing premise): treat
   as Branch B and ship the n=9 anchor instead; cycle 299 re-submits
   to Aristotle with the corrected premise.

**DO NOT** spend more than 30 minutes on error remediation. If
remediation is non-trivial, defer to cycle 299 and ship Branch B.

## Priority 5 (P5) — Branch D (if Aristotle FAILED/CANCELLED)

Pivot to manual closure per `.prover-state/issues/lem_342A_g_zeros_scoping.md`:
1. Cancel any other pending Aristotle jobs to free the slot.
2. Update the issue file with a Branch D entry recording the failure.
3. Re-submit with a strengthened prompt that includes worked examples
   of sign-change extraction in `Polynomial`-over-ℝ.
4. **Also ship n=9 anchor** as Branch B safety net.

## What NOT to do this cycle

- **Do NOT poll Aristotle more than once.** CLAUDE.md is explicit; one
  poll per cycle. The cycle 282–286 precedent confirmed this discipline
  works.
- **Do NOT cancel `5939f28b` at observation #2.** The three-stall
  protocol requires three consecutive flat readings (obs #1 from cycle
  297, obs #2 from cycle 298, obs #3 from cycle 299) before cancelling.
- **Do NOT attempt the general (342g) statement manually.** While
  Aristotle is healthy (or only at stall obs #2), manual closure is
  forbidden per the cycle 297 strategy §F.1 and cycle 285 protocol.
  Cycle 300 is the earliest cycle that may cancel and pivot manual.
- **Do NOT raise `maxHeartbeats` above 200000.** If n=9 evaluations
  blow past, decompose into private helpers per cycle 281's pattern.
- **Do NOT introduce `axiom` or `constant` declarations.**
- **Do NOT introduce `sorry`.** Cycle 298's deliverables must be
  axiom-clean or skipped entirely. If P2 stalls, ship nothing and
  document — do not leave a sorry behind.
- **Do NOT skip the bracket sanity-check.** Pre-compute every
  endpoint sign with Python `Fraction` arithmetic BEFORE writing the
  Lean proof. Cycle 296/297 used hand verification; cycle 298's larger
  bracket count makes this non-optional.
- **Do NOT pivot to a fresh entity.** §342 (342g) is the current
  target, and n=9 is the natural anchor extension. Pivot only if
  Aristotle FAILS (Branch D), in which case the pivot is to the manual
  closure plan, not a new entity.
- **Do NOT attempt `lem:342B` (Gaussian quadrature).** It depends on
  (342g) for the existence of nodes; blocked until (342g) lands.
- **Do NOT modify** `scripts/autonomous_loop.py` or any other
  supervisor infrastructure.

## What you actually do this cycle (concrete checklist)

1. **(2 min)** Single-poll Aristotle `5939f28b` via
   `mcp__aristotle__get_status`.
2. **(1 min)** Dispatch on result per the branch table above. Most
   likely outcome: IN_PROGRESS at 25% → Branch B.
3. **Branch B path (most likely, ~90 min)**:
   a. Pre-compute the 8 IVT bracket endpoint evaluations of `P_9^*`
      via Python `Fraction` (one-liner script if needed) to confirm
      signs match the bracket plan above.
   b. Adjust bracket denominators if any sign mismatches.
   c. Open `OpenMath/Chapter3/Section342.lean` and append
      `butcherShiftedLegendre_nine_roots` after cycle 297's
      `butcherShiftedLegendre_seven_roots` (around line ~4196).
   d. Mechanical port of cycle 297's recipe: 8 IVT applications + 1
      parity helper + 36-pair distinctness `linarith` chain.
   e. `lake build OpenMath.Chapter3.Section342` to verify.
   f. `#print axioms butcherShiftedLegendre_nine_roots` for axiom
      check.
   g. Append cycle 298 stall observation #2 update to
      `.prover-state/issues/lem_342A_g_zeros_scoping.md`.
4. **Write task results** to
   `.prover-state/task_results/cycle_298.md` per the CLAUDE.md format.
5. **Commit and push** with a message like
   `Cycle 298 — §342 (342g) n=9 empirical anchor + Aristotle obs #2.`

## Stretch (P6, only if cycle has spare budget)

If Branch B ships in < 60 min and `lake build` is clean, consider:

- **Cross-check witness**: state and prove
  `butcherShiftedLegendre_seven_roots_distinct_from_zero` (a corollary
  of the cycle 297 theorem confirming all 7 roots are non-zero — trivial
  from `r_i ∈ Ioo 0 1` so `r_i > 0`, but useful for downstream
  `lem:342B` consumers). ~10 LOC.
- **Sanity helper**: `butcherShiftedLegendre_n_roots_le_n` —
  `(P_n^*).roots.toFinset.card ≤ n` for ANY `n`, generalising cycle
  294's `butcherShiftedLegendre_card_roots_le`. May already be implied;
  audit.

DO NOT take on P6 unless Branch B completed comfortably.

## Bottom line

Cycle 298 is a continuation: one Aristotle poll, then ship n=9 anchor
on the most-likely IN_PROGRESS branch. ~340 LOC mechanical port of
cycle 297. Axiom-clean expected; no infrastructure work needed.
