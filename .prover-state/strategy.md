# Cycle 281 strategy

## Status snapshot (end of cycle 280)

- `OpenMath/Chapter3/Section342.lean`: 1740 LOC, 0 sorries, axiom-clean.
- Ladder rungs `_zero` through `_seven` shipped for both
  `butcherShiftedLegendre_*` and `butcherShiftedLegendre_norm_sq_*`.
- Aristotle project `d4ce527b-b714-4e51-b0a6-e3d06302d7fa` (general
  (342d) `∫₀¹ (P_n^*(x))² dx = 1/(2n+1)`): **IN_PROGRESS at 58%** as of
  cycle 280 single poll (trajectory: 33% → 52% → 58% over cycles
  278/279/280).
- (342a) orthogonality, (342b), (342c), (342e), and seven concrete
  (342d) instances all shipped. Open within §342: (342d) general,
  (342f) three-term recurrence, (342g) `n` distinct real zeros.

## Priority 0 — Single Aristotle poll (5 min)

Call `mcp__aristotle__get_status` **exactly once** on project
`d4ce527b-b714-4e51-b0a6-e3d06302d7fa`. Do NOT re-poll within this
cycle. Do NOT cancel the job.

### Branch A — Aristotle returned COMPLETE

If status is `COMPLETE`:

1. Call `mcp__aristotle__download_result` and inspect
   `ARISTOTLE_SUMMARY.md` + the returned `.lean` file.
2. Identify any helper lemmas Aristotle introduced (Rodrigues-style
   helpers, IBP × n machinery, factorial / beta-integral bridges).
3. Compare Aristotle's helpers against what is already in
   `Section342.lean` (lines 271–1043 from cycle 277 (342a)
   integration: `iterDeriv_XnOneSubXn_eval_zero`,
   `iterDeriv_XnOneSubXn_eval_one`, `poly_ibp`,
   `integral_poly_mul_iterDeriv_vanish`). Reuse these where possible
   rather than introducing duplicates.
4. Adapt Aristotle's namespaces to `OpenMath.Chapter3.Section342` (per
   cycle 277 precedent: change Mathlib path roots from any stub forms
   Aristotle assumed back to canonical names).
5. Rewrite IBP chains using
   `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`
   rather than `integral_deriv_eq_sub'` if Aristotle picked the
   latter (cycle 277 lesson — the latter form had parser issues with
   nested by-blocks).
6. Ship a single public theorem
   `butcherShiftedLegendre_norm_sq (n : ℕ) :
   ∫ x in (0:ℝ)..1, (butcherShiftedLegendre n).eval x ^ 2 =
   1 / (2 * (n : ℝ) + 1)`.
7. Verify the seven concrete `_norm_sq_*` lemmas (cycles 274–280)
   still build via `lake build OpenMath.Chapter3.Section342`. They
   should remain valid as numerical witnesses of the general theorem.
8. `lean_status.json` and `plan.md`: mark `lem:342A` as `partial`
   (or upgrade further if the integration closes more clauses).
9. Verify axiom-cleanliness via `#print axioms` — must return
   `[propext, Classical.choice, Quot.sound]` only.
10. Skip to "Closing this cycle" section below.

### Branch B — Aristotle returned IN_PROGRESS or FAILED

Proceed to Priority 1. Leave the Aristotle job running (do NOT
cancel).

## Priority 1 — File split (the cycle 280 recommendation)

Section342.lean is now 1740 LOC. Cycle 280's discovery #4 confirmed
we are at the natural split boundary. Adding n=8 would push to
~1990 LOC. The file split provides organizational benefit without
new mathematical risk, and is the lowest-risk single-cycle
deliverable when Aristotle hasn't returned.

### Task 1.1 — Create new file `OpenMath/Chapter3/Section342NormSquare.lean`

Move the following declarations from `Section342.lean` to a new file
`OpenMath/Chapter3/Section342NormSquare.lean`:

- All eight `butcherShiftedLegendre_<zero|one|two|three|four|five|six|seven>`
  closed-form expansions (cycles 271, 273, 275, 276, 277, 278, 279,
  280).
- All eight `butcherShiftedLegendre_norm_sq_<zero|one|two|three|four|five|six|seven>`
  integral evaluations (cycles 274, 274, 275, 276, 277, 278, 279,
  280).
- The eight non-vacuity `example`s (one per `_norm_sq_*` matching
  the `1/(2n+1)` closed form).

Keep in `Section342.lean`:
- `butcherShiftedLegendre` definition (cycle 271).
- `butcherShiftedLegendre_eval_one` (342b) and
  `butcherShiftedLegendre_eval_one_sub` (342c) (cycle 271).
- `butcherShiftedLegendre_rodrigues` (342e) (cycle 272).
- `butcherShiftedLegendre_natDegree` (cycle 272).
- `butcherShiftedLegendre_eval_zero` (cycle 273 helper).
- `butcherShiftedLegendre_orthogonal` (342a) (cycle 277) along with
  its four helpers `iterDeriv_XnOneSubXn_eval_zero`,
  `iterDeriv_XnOneSubXn_eval_one`, `poly_ibp`,
  `integral_poly_mul_iterDeriv_vanish`.

### Task 1.2 — Imports in the new file

`Section342NormSquare.lean` needs:

```lean
import OpenMath.Chapter3.Section342
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
```

The first import gives access to `butcherShiftedLegendre` plus all
the helpers from `Section342.lean`. The second gives `integral_pow`,
`integral_one`, `intervalIntegral.integral_const`,
`intervalIntegral.integral_add`, etc.

Namespace: `namespace OpenMath.Chapter3.Section342` (same as
`Section342.lean` so dot-notation continues to work).

### Task 1.3 — Update the chapter aggregator

Update `OpenMath/Chapter3.lean` to add
`import OpenMath.Chapter3.Section342NormSquare` immediately after the
existing `import OpenMath.Chapter3.Section342`.

### Task 1.4 — Verification

```bash
lake env lean OpenMath/Chapter3/Section342.lean
lake env lean OpenMath/Chapter3/Section342NormSquare.lean
lake env lean OpenMath/Chapter3.lean
grep -c sorry OpenMath/Chapter3/Section342.lean
grep -c sorry OpenMath/Chapter3/Section342NormSquare.lean
```

All must succeed with exit 0 and 0 sorries in each file. No
`#print axioms` regression expected — the move is purely
organizational.

If `Section342NormSquare.lean` fails to compile due to missing
helper imports (e.g. a closed-form expansion references a helper
that remained in `Section342.lean`), the helper accesses go through
the namespace, so no additional imports should be needed beyond
`OpenMath.Chapter3.Section342`. If something does fail, the most
likely culprit is a missing
`Mathlib.Analysis.SpecialFunctions.Integrals.Basic` import — verify
by trying to elaborate a one-line `example` invoking `integral_pow`
in the new file.

## Priority 2 (only if 1 completes with significant time to spare) — n=8 ladder rung

If Priority 1's file split lands cleanly with significant cycle
budget remaining (unlikely given the move + verification overhead),
extend the ladder to n=8 in the new `Section342NormSquare.lean`:

### Task 2.1 — `butcherShiftedLegendre_eight`

Apply the cycle 279 even-`n` template (since `(-1)^8 = +1`):

- `unfold butcherShiftedLegendre; ext k`.
- `simp only [coeff_C_mul, coeff_map, coeff_shiftedLegendre]`.
- `match k with | 0 => … | 1 => … | … | 8 => … | k + 9 => …`.
- For each `k ∈ {0..8}` arm: pre-compute `Nat.choose 8 k` and
  `Nat.choose (8+k) 8` via `decide`-helpers, then `norm_num`.
- Catch-all `k + 9`: `Nat.choose_eq_zero_of_lt`.

**Pre-compute the closed-form coefficients in Python first** before
writing any Lean. Use SymPy or `fractions.Fraction`:

```python
from sympy import symbols, Poly, sqrt
from math import comb
x = symbols('x')
n = 8
P_n_star = sum((-1)**(n-k) * comb(n, k) * comb(n+k, n) * x**k for k in range(n+1))
print(Poly(P_n_star, x).all_coeffs())
```

Cross-check `P_8^*(1) = 1` and `P_8^*(0) = (-1)^8 = +1` (so constant
term should be `+1`).

### Task 2.2 — `butcherShiftedLegendre_norm_sq_eight`

Apply the cycle 279/280 pattern:

- Pre-compute the 17-coefficient convolution of `(P_8^*)^2` via Python
  with `fractions.Fraction`. Cross-check `c_0 = 1`,
  `c_16 = (lead_coef)^2`, and `Σ c_k/(k+1) = 1/17` BEFORE any Lean
  code.
- 16 `IntervalIntegrable` witnesses `hi_x16, …, hi_x`.
- 16 `integral_pow` evaluations.
- 16-deep cascade of `integral_add`/`integral_sub`, leading paren
  count `16` on the outermost level (per cycle 280 closed-form
  formula: leading parens = 2n).
- 16 `integral_const_mul` to factor leading constants.
- `ring` closes the 17-fraction sum to `1/17`.

Non-vacuity: `example : (1 : ℝ) / (2 * (8 : ℕ) + 1) = 1/17 := by
norm_num`.

**Skip Priority 2 entirely if Priority 1 takes the full cycle.**
File splits typically take 60–90 min when redistributing 700+ LOC
across imports and verifying no regressions.

## What NOT to try (failed approaches from prior cycles)

Do NOT attempt any of these — they have been ruled out by previous
cycles:

1. **(342f) three-term recurrence** (cycle 273 dead end): both
   `Polynomial.ext` (coefficient route) and `Polynomial.funext` (eval
   route) require Pascal-style binomial identities on `Nat.choose`
   that `ring` cannot close. Butcher's degree-and-difference outline
   requires (342a) orthogonality as input — even with orthogonality
   now in hand (cycle 277), the recurrence requires either Bonnet-
   recurrence machinery (absent from Mathlib) or substantial standard-
   Legendre infrastructure to bootstrap. Not single-cycle.

2. **(342g) `n` distinct real zeros** (deferred since cycle 271):
   requires Sturm sequence or oscillation arguments not yet in scope.
   Not single-cycle.

3. **Aristotle re-polling within a cycle** (CLAUDE.md): one
   `mcp__aristotle__get_status` per cycle, period. The 58% → ?
   progress trajectory does not justify additional polls.

4. **Aristotle cancellation**: project `d4ce527b` is healthy with
   visible progress; cancelling now would waste 58% of accumulated
   compute. Leave it running.

5. **Even-`n` recipe at odd `n` or vice versa** (cycle 277 lesson):
   the outer `C ((-1)^n) * ·` Butcher sign factor MUST be peeled off
   via `simp only [coeff_C_mul, coeff_map, coeff_shiftedLegendre]`
   BEFORE the per-`k` `match`. Naive `simp […]; ring` collapses
   `C((-1)^n)` and breaks coefficient extraction for `n ≥ 3`.

6. **Compile `Section441.lean`** (43+ consecutive GPFS timeouts since
   cycle 182): per `.prover-state/issues/cycle_182_gpfs_slowness.md`,
   skip any §441 path. Loop-maintainer territory.

7. **Sorry-first scaffolds** for multi-cycle work (cycle 138/139,
   149/150, 200/201 rollback precedent). If any deliverable in this
   cycle cannot land axiom-clean, do NOT introduce sorries — abort
   the deliverable and document the abort in task results.

8. **Modifying `scripts/autonomous_loop.py`** (per CLAUDE.md and
   `tautology_scanner_false_positives.md`): loop-maintainer
   territory.

9. **Pivot to a fresh entity** (e.g. `thm:344A`, `lem:342B`)
   this cycle. Cycle 280's task results listed this as an option,
   but the file split is the higher-priority single-cycle deliverable
   given that we are at the LOC threshold and the cycle 280 worker
   explicitly recommended it. A fresh entity is the cycle 282+ option
   if Aristotle continues to stall and the ladder/split paths are
   exhausted.

## Closing this cycle

After completing the deliverables above:

1. Run final verification:
   ```bash
   lake env lean OpenMath/Chapter3/Section342.lean
   lake env lean OpenMath/Chapter3/Section342NormSquare.lean   # if created
   lake env lean OpenMath/Chapter3.lean
   ```
2. Confirm 0 sorries across all touched files.
3. Spot-check axiom-cleanliness on any new public theorems:
   ```
   #print axioms <new theorem>
   ```
   Must return `[propext, Classical.choice, Quot.sound]`.
4. Write `.prover-state/task_results/cycle_281.md` documenting:
   - Aristotle poll result (Branch A or B taken).
   - File split status (LOC moved, files touched).
   - Any unexpected issues encountered.
   - Faithfulness check on any new theorems.
   - Suggested next approach for cycle 282 (continue ladder? wait
     for Aristotle? pivot to fresh entity?).
5. If `lean_status.json` rows change (only on Branch A integration),
   update the entry and bump `formalization_cycle`.
6. Update `plan.md` only if entity statuses change.
7. Commit and push per CLAUDE.md guidance.

## Cycle budget guidance

- Priority 0 (Aristotle poll): 5 min.
- Priority 1 (file split): 60–90 min including verification.
- Priority 2 (n=8 rung): only if substantial budget remains after
  Priority 1; skip otherwise.

Total target: 1–1.5 hours of focused work, axiom-clean ship.
