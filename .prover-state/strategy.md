# Cycle 276 Strategy — §342 (342d) ladder at n=3 + Aristotle poll

## Context (carry-over from cycle 275)

Cycle 275 shipped axiom-clean:
* `butcherShiftedLegendre_two : P_2^* = 6X² - 6X + 1`
* `butcherShiftedLegendre_norm_sq_two : ∫₀¹ (P_2^*)² = 1/5`

The (342d) ladder is now at `n ∈ {0, 1, 2}`. The full general
(342d) `∫₀¹ (P_n^*)² = 1/(2n+1)` remains submitted to Aristotle.
Section342.lean: 491 LOC, 0 sorries, axiom-clean.

Two Aristotle projects remain IN_PROGRESS as of cycle 275 poll:
* `727396d5-14f9-4014-9aad-1f38238a1651` — (342a) orthogonality, at 22%
* `d4ce527b-b714-4e51-b0a6-e3d06302d7fa` — (342d) general norm-square, at 11%

## Priority 0 — Aristotle single-poll (MANDATORY, ~3 min)

Run `mcp__aristotle__get_status` ONCE for each of the two projects.
**Do NOT poll twice.** Per CLAUDE.md, one check per cycle is enough.

```
mcp__aristotle__get_status(project_id="727396d5-14f9-4014-9aad-1f38238a1651")
mcp__aristotle__get_status(project_id="d4ce527b-b714-4e51-b0a6-e3d06302d7fa")
```

### Branching on poll results

**Branch A: `727396d5` (342a) returns `COMPLETED` (or terminal success)**:
  Download via `mcp__aristotle__download_result` and inspect.
  Integrate the (342a) orthogonality proof into Section342.lean as
  `butcherShiftedLegendre_orthogonal : m ≠ n → ∫₀¹ P_m^* · P_n^* = 0`.
  This closes the headline `lem:342A` clause (342a). Update
  `lean_status.json` and `plan.md` row accordingly. SKIP Priority 1.

**Branch B: `d4ce527b` (342d) returns `COMPLETED`**:
  Download and inspect. If it proves the general
  `butcherShiftedLegendre_norm_sq : ∫₀¹ (P_n^*)² = 1/(2n+1)`,
  integrate as the headline (342d) result and supersede the cycle
  274/275 special cases (n=0, 1, 2) — keep them as corollaries or
  remove if redundant. SKIP Priority 1.

**Branch C: Both still IN_PROGRESS or FAILED**:
  Proceed to Priority 1 (extend the ladder to n=3).

**Branch D: Either returns `COMPLETE_WITH_ERRORS`**:
  Inspect the error. If a one-line namespace/import fix (cf. cycle 184
  precedent), apply it and re-verify. Otherwise document the failure
  in task results and skip to Priority 1.

## Priority 1 — Manual (342d) at n=3 (~80–120 LOC if no Aristotle hit)

Extend the cycle 274/275 ladder one rung: ship
`butcherShiftedLegendre_three : P_3^* = 20X³ - 30X² + 12X - 1` AND
`butcherShiftedLegendre_norm_sq_three : ∫₀¹ (P_3^*(x))² dx = 1/7`.

### Step 1: `butcherShiftedLegendre_three` (~35 LOC)

Mirror cycle 275's `butcherShiftedLegendre_two` recipe. From
`Polynomial.coeff_shiftedLegendre` at `n = 3`:
`(shiftedLegendre 3).coeff k = (-1)^k · C(3,k) · C(3+k, 3)`.

| k | (-1)^k | C(3,k) | C(3+k, 3) | product |
|---|--------|--------|-----------|---------|
| 0 | 1 | 1 | 1 | 1 |
| 1 | -1 | 3 | 4 | -12 |
| 2 | 1 | 3 | 10 | 30 |
| 3 | -1 | 1 | 20 | -20 |
| ≥4 | — | 0 | — | 0 |

So `shiftedLegendre 3 = -20X³ + 30X² - 12X + 1` over ℤ. Then
`butcherShiftedLegendre 3 = (-1)^3 · (shiftedLegendre 3 cast to ℝ)
= 20X³ - 30X² + 12X - 1` (the leading sign flips because `(-1)^3 = -1`).

**Critical sign check**: Verify by evaluating at x=1:
`butcherShiftedLegendre 3 |_{x=1} = 20 - 30 + 12 - 1 = 1` ✓
(matches `butcherShiftedLegendre_eval_one`, which is always 1).
Also at x=0: `(-1)^3 · ((-1)^0 · C(3,0) · C(3,3)) = -1 · 1 · 1 = -1` ✓
(matches `butcherShiftedLegendre_eval_zero` from cycle 273:
`P_n^*(0) = (-1)^n`).

Proof recipe (mirrors cycle 275):
1. `Polynomial.ext` + `match` on `k ∈ {0, 1, 2, 3, k+4}`.
2. For `k = 2`: `Nat.choose 5 3 = 10` via `decide`.
3. For `k = 3`: `Nat.choose 6 3 = 20` via `decide`.
4. For `k + 4` tail: `Nat.choose_eq_zero_of_lt` (since `3 < k + 4`).

### Step 2: `butcherShiftedLegendre_norm_sq_three` (~60 LOC)

Expand `(20x³ - 30x² + 12x - 1)²`. Let `a = 20x³, b = -30x², c = 12x, d = -1`:
* `a² = 400x⁶`
* `2ab = -1200x⁵`
* `2ac + b² = 480x⁴ + 900x⁴ = 1380x⁴`
* `2ad + 2bc = -40x³ - 720x³ = -760x³`
* `2bd + c² = 60x² + 144x² = 204x²`
* `2cd = -24x`
* `d² = 1`

So `(20x³ - 30x² + 12x - 1)² = 400x⁶ - 1200x⁵ + 1380x⁴ - 760x³ + 204x² - 24x + 1`.

Integrating on `[0, 1]`:
`400/7 - 1200/6 + 1380/5 - 760/4 + 204/3 - 24/2 + 1`
`= 400/7 - 200 + 276 - 190 + 68 - 12 + 1`
`= 400/7 - 57`
`= 400/7 - 399/7 = 1/7` ✓

Proof recipe (extends cycle 275's 5-monomial split to 7):
1. `rw [butcherShiftedLegendre_three]`.
2. Reduce integrand to `400x⁶ - 1200x⁵ + 1380x⁴ - 760x³ + 204x² - 24x + 1`
   pointwise via `simp [Polynomial.eval_*]` + `ring`.
3. Split via nested `intervalIntegral.integral_add` / `integral_sub` ×6 plus
   `integral_const_mul` ×6.
4. Close each `∫₀¹ x^k` via `integral_pow` for `k ∈ {2, 3, 4, 5, 6}`.
5. `∫₀¹ x = 1/2` uses the cycle 274/275 trick: `integral_pow` at exponent 1
   produces `(1 - 0)/(1 + 1)` but needs
   `simp only [pow_one, Nat.cast_one]` to normalize.
6. `∫₀¹ 1 = 1` via `integral_one`.
7. Final arithmetic via `norm_num` or `ring`.

### Step 3: Non-vacuity witness (~3 LOC)

```lean
example : ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre 3).eval x ^ 2
    = 1 / (2 * (3 : ℕ) + 1) := by
  rw [butcherShiftedLegendre_norm_sq_three]; norm_num
```

Confirms match to `1/(2n+1)` at `n = 3`.

### Step 4: Verification

* `mcp__lean-lsp__lean_diagnostic_messages` on `Section342.lean` → 0 errors, 0 warnings.
* `mcp__lean-lsp__lean_verify` on `butcherShiftedLegendre_three` and
  `butcherShiftedLegendre_norm_sq_three` → axiom-clean
  `[propext, Classical.choice, Quot.sound]`.

## Priority 2 — Fallback if P1.Step 2 stalls (~35 LOC)

If the `norm_sq_three` proof stalls (e.g. the 7-monomial integral
split blows past the cycle budget), ship JUST
`butcherShiftedLegendre_three` (the expansion lemma) without the
integral, and defer `_norm_sq_three` to cycle 277. The expansion
lemma alone is useful infrastructure for any future (342f) recurrence
attempt or (342g) zeros analysis.

**Time-box rule**: If the `norm_sq_three` `ring`/`simp` step exceeds
~60s wall on its first compile attempt, fall back to P2 immediately.
Do not retry with different tactic permutations.

## What NOT to attempt

* **DO NOT retry (342f) three-term recurrence.** Cycle 273 documented
  conclusively that `Polynomial.funext + ring` and `Polynomial.ext` both
  require Pascal-style binomial identities on `Nat.choose` that `ring`
  cannot close, and there is no standard Legendre infrastructure in
  Mathlib. (342f) requires (342a) orthogonality as input first.

* **DO NOT attempt (342g) real-zeros-in-(0,1).** This requires complex
  analysis machinery (Rolle's theorem on iterated derivatives of
  `x^n(1-x)^n` via Rodrigues) not yet built.

* **DO NOT poll Aristotle more than once per project this cycle.**
  CLAUDE.md is explicit; cycles 274/275 followed it correctly.

* **DO NOT submit new Aristotle jobs.** The two existing projects are
  still in flight; submitting more dilutes the worker queue.

* **DO NOT compile `Section441.lean`.** GPFS pathology unchanged (43rd
  consecutive timeout as of cycle 239). Skip per
  `cycle_182_gpfs_slowness.md`.

* **DO NOT introduce sorries.** Cycle 200/201 rollback precedent
  applies: ship axiom-clean or skip the step.

* **DO NOT raise `maxHeartbeats` above 200000.** If the 7-monomial
  `ring` stalls, fall back to P2.

* **DO NOT update `lean_status.json` for `lem:342A`.** It stays
  `partial` this cycle (n=3 is one more stepping stone toward the
  general (342d), not closure).

## Failed approaches to AVOID (from attempts.md)

* `Polynomial.ext + simp + ring` on closed forms with `Polynomial.C`
  rational arithmetic (cycle 172/173 pattern): `ring` cannot fold
  `Polynomial.C` constants over rationals. Use `Polynomial.funext + ring`
  if needed, OR per-coefficient `Polynomial.ext` with explicit
  `coeff_*` rewrites (this is what cycles 273/275 used successfully).

* `simp only [Polynomial.coeff_*]` without `Nat.choose` evaluations:
  `simp` does not unfold `Nat.choose` automatically. Always supply
  `decide` for explicit `Nat.choose m k = v` evaluations.

* Plain `rw` on (342f)-style polynomial identities: Pascal identities
  on `Nat.choose` cannot be discharged by `ring` (cycle 273 dead end).

## Faithfulness check (mandatory before commit)

For `butcherShiftedLegendre_three`:
* This is helper infrastructure for `lem:342A`, not a textbook-named
  theorem. The cycle 273/275 precedent for `_one` and `_two` established
  the convention: each `_n` expansion lemma is auxiliary, not entity-level.
* Verify leading-coefficient sign: `(-1)^n` factor matters at odd `n`.
  Sanity-check via `eval_one` (= 1) and `eval_zero` (= (-1)^3 = -1).
* Identity check: proof is NOT `exact h_anything`; it does real work
  via `Polynomial.ext` + per-coefficient computation.

For `butcherShiftedLegendre_norm_sq_three`:
* Quote Butcher (342d): `∫₀¹ P_n^*(x)^2 dx = 1/(2n+1)`. At `n = 3`,
  this is `1/7` (which matches Lean's conclusion).
* Tautology check: `= 1/7` is not equal to any hypothesis.
* Identity check: proof does real integration work, not a hypothesis
  re-export.

## Commit message template

```
Cycle 276 — §342 (342d) n=3 case + butcherShiftedLegendre_three SHIPPED.

* butcherShiftedLegendre_three: P_3^* = 20X³ - 30X² + 12X - 1
* butcherShiftedLegendre_norm_sq_three: ∫₀¹ (P_3^*)² = 1/7
* Aristotle (342a) project 727396d5: poll result <status>%
* Aristotle (342d) project d4ce527b: poll result <status>%

Section342.lean: <new LOC>, 0 sorries, axiom-clean.
```

(If P2 fallback fires: omit `norm_sq_three` from the message and note
the deferral in task results.)

## Pre-commit checklist

1. `mcp__lean-lsp__lean_diagnostic_messages` on `OpenMath/Chapter3/Section342.lean` → 0 errors, 0 warnings.
2. `mcp__lean-lsp__lean_verify` on every new theorem → `[propext, Classical.choice, Quot.sound]` only.
3. `grep -c sorry OpenMath/Chapter3/Section342.lean` → 0.
4. Task results written to `.prover-state/task_results/cycle_276.md` with:
   - Aristotle poll results documented
   - Faithfulness check per new theorem
   - Discovery notes (e.g. `Nat.choose` evaluations needed)
   - Suggested next approach for cycle 277
5. `plan.md` row for `lem:342A` does NOT change (stays `[~]`).
6. `lean_status.json` row for `lem:342A` does NOT change (stays `partial`).
7. Git commit and verify push lands.

## Verification commands at cycle start

```bash
git log -1 --format='%H %s'
# Expected: c48a59f Cycle 275 — §342 (342d) n=2 case + butcherShiftedLegendre_two SHIPPED.

wc -l OpenMath/Chapter3/Section342.lean
# Expected: ~491

grep -c sorry OpenMath/Chapter3/Section342.lean
# Expected: 0
```

Confirms cycle 275 is at HEAD before extending.
