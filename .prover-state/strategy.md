# Cycle 280 Strategy

## Context

Cycle 279 SHIPPED §342 (342d) n=6 ladder rung axiom-clean (`butcherShiftedLegendre_six` + `butcherShiftedLegendre_norm_sq_six`). Section342.lean is 1466 LOC, 0 sorries, 0 warnings.

Aristotle project `d4ce527b-b714-4e51-b0a6-e3d06302d7fa` (general (342d) proof) was at **52%** at cycle 279's poll, up from 33% in cycle 278 — a remarkable +19pp jump in one cycle. Completion by cycle 280 or 281 is plausible.

§342 (342a) orthogonality landed via Aristotle in cycle 277. The remaining (342) clauses are:
- (342d) general — Aristotle in progress (52%)
- (342f) three-term recurrence — blocked on Mathlib Legendre infra
- (342g) `n` distinct real zeros — deferred

## Priority 0 — Poll Aristotle `d4ce527b` (BLOCKING, do this FIRST)

Call `mcp__aristotle__get_status` on project `d4ce527b-b714-4e51-b0a6-e3d06302d7fa`. **Do NOT re-poll.** Single poll only per CLAUDE.md.

### Branch A: Aristotle returns COMPLETE

Integrate the general (342d) result. Recipe (mirror cycle 277's (342a) integration):

1. Download the result file via `mcp__aristotle__download_result` to `.prover-state/aristotle_results/cycle_280/`.
2. Read `ARISTOTLE_SUMMARY.md` and the returned `.lean` file.
3. Inline the helper lemmas + main theorem into `OpenMath/Chapter3/Section342.lean`. Likely additions:
   - Iterated integration by parts × n (similar to cycle 277's `integral_poly_mul_iterDeriv_vanish`)
   - Beta integral on ℕ-exponents (`∫₀¹ x^n (1-x)^n dx = (n!)^2 / (2n+1)!`)
   - Main result: `butcherShiftedLegendre_norm_sq : ∀ n, ∫₀¹ (butcherShiftedLegendre n).eval x ^ 2 ∂x = 1 / (2 * n + 1)`
4. Rewrite the cycle 274–279 concrete `_norm_sq_{zero..six}` witnesses as one-line corollaries of the general result via `simp` / `norm_num` (or keep them as standalone witnesses if simpler).
5. Update `lean_status.json`: `lem:342A` may move from `partial` → `partial` (still missing 342f, 342g) but document (342d) is now closed in `plan.md`.
6. `#print axioms` must return `[propext, Classical.choice, Quot.sound]`. If `MeasureTheory` axioms appear, that is expected for integral results.
7. Verify build: `lake env lean OpenMath/Chapter3/Section342.lean` + `lake env lean OpenMath/Chapter3.lean`.

If Aristotle's proof has compile errors (likely surfaces in `COMPLETE_WITH_ERRORS` status), apply minimal fixes (namespace qualifications, simp set adjustments) per the cycle 277 / cycle 184 pattern.

### Branch B: Aristotle returns IN_PROGRESS

Proceed to Priority 1 (manual n=7 ladder rung). Do not cancel the Aristotle job.

### Branch C: Aristotle returns COMPLETE_WITH_ERRORS

Download the result, identify the specific errors, apply fixes locally. If errors are non-trivial (>30 min to fix), pivot to Priority 1 and revisit next cycle.

## Priority 1 — Ship `n = 7` ladder rung (BRANCH B fallback)

Add two new public theorems to `OpenMath/Chapter3/Section342.lean`:

### 1.1 `butcherShiftedLegendre_seven`

**Target:**
```lean
theorem butcherShiftedLegendre_seven :
    butcherShiftedLegendre 7 =
      Polynomial.C 3432 * Polynomial.X ^ 7
      - Polynomial.C 12012 * Polynomial.X ^ 6
      + Polynomial.C 16632 * Polynomial.X ^ 5
      - Polynomial.C 11550 * Polynomial.X ^ 4
      + Polynomial.C 4200 * Polynomial.X ^ 3
      - Polynomial.C 756 * Polynomial.X ^ 2
      + Polynomial.C 56 * Polynomial.X
      - Polynomial.C 1
```

**Coefficients (verified in cycle 279 task results, odd-`n` so outer `(-1)^7 = -1` flips signs):**

| k | (-1)^k | C(7,k) | C(7+k,7) | inner | outer (·(-1)) | coeff(k) |
|---|--------|--------|----------|-------|---------------|----------|
| 0 |   1    |   1    |    1     |   1   |     -1        |    -1    |
| 1 |  -1    |   7    |    8     |  -56  |     56        |    56    |
| 2 |   1    |  21    |   36     |  756  |    -756       |   -756   |
| 3 |  -1    |  35    |  120     | -4200 |    4200       |   4200   |
| 4 |   1    |  35    |  330     | 11550 |   -11550      |  -11550  |
| 5 |  -1    |  21    |  792     |-16632 |    16632      |   16632  |
| 6 |   1    |   7    | 1716     | 12012 |   -12012      |  -12012  |
| 7 |  -1    |   1    | 3432     | -3432 |    3432       |   3432   |

**Sanity checks:**
- At x=1: `3432 - 12012 + 16632 - 11550 + 4200 - 756 + 56 - 1 = 1` ✓ (matches (342b))
- At x=0: constant = -1 = `(-1)^7` ✓ (matches `butcherShiftedLegendre_eval_zero`)

**Recipe (mirror cycle 278's `_five` template, odd-`n` case):**

```lean
theorem butcherShiftedLegendre_seven :
    butcherShiftedLegendre 7 = ... := by
  unfold butcherShiftedLegendre
  ext k
  -- Peel off `C ((-1)^7) * ·` BEFORE simp can collapse it
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map,
             Polynomial.coeff_shiftedLegendre]
  match k with
  | 0 => simp; norm_num
  | 1 => simp; norm_num
  | 2 =>
    have h2a : Nat.choose 7 2 = 21 := by decide
    have h2b : Nat.choose 9 7 = 36 := by decide
    simp [h2a, h2b]; norm_num
  | 3 =>
    have h3a : Nat.choose 7 3 = 35 := by decide
    have h3b : Nat.choose 10 7 = 120 := by decide
    simp [h3a, h3b]; norm_num
  | 4 =>
    have h4a : Nat.choose 7 4 = 35 := by decide
    have h4b : Nat.choose 11 7 = 330 := by decide
    simp [h4a, h4b]; norm_num
  | 5 =>
    have h5a : Nat.choose 7 5 = 21 := by decide
    have h5b : Nat.choose 12 7 = 792 := by decide
    simp [h5a, h5b]; norm_num
  | 6 =>
    have h6a : Nat.choose 7 6 = 7 := by decide
    have h6b : Nat.choose 13 7 = 1716 := by decide
    simp [h6a, h6b]; norm_num
  | 7 =>
    have h7 : Nat.choose 14 7 = 3432 := by decide
    simp [h7]; norm_num
  | k + 8 =>
    -- Coefficient is 0 for k ≥ 8
    simp [Nat.choose_eq_zero_of_lt (by omega : 7 < k + 8)]
```

Adjust the per-arm `simp` set / `norm_num` invocation based on what fires; the cycle 278 template should port mechanically. Verify against `mcp__lean-lsp__lean_hover_info` on `Polynomial.coeff_shiftedLegendre` if the formula doesn't unfold as expected.

### 1.2 `butcherShiftedLegendre_norm_sq_seven`

**Target:**
```lean
theorem butcherShiftedLegendre_norm_sq_seven :
    ∫ x in (0:ℝ)..1, (butcherShiftedLegendre 7).eval x ^ 2 = 1 / 15
```

**Strategy:**
1. Use `butcherShiftedLegendre_seven` to rewrite the integrand to an explicit degree-14 polynomial in `x` (the square of the closed form).
2. Compute the 15 convolution coefficients `c_0..c_14` of `(P_7^*)^2` BEFORE writing Lean.
3. Apply 14 nested `intervalIntegral.integral_add` / `integral_sub` + 14 `integral_const_mul` + 14 `integral_pow` ops (`∫₀¹ x^k = 1/(k+1)`).
4. Close with `ring` to collapse the 15-fraction sum to `1/15`.

**Convolution computation** (compute by hand BEFORE writing Lean; use Python or careful arithmetic):

With `a_0..a_7 = (-1, 56, -756, 4200, -11550, 16632, -12012, 3432)`,
`c_k = Σ_{i+j=k} a_i · a_j`:

- `c_0 = a_0^2 = (-1)^2 = 1`
- `c_14 = a_7^2 = 3432^2 = 11778624`

Compute the intermediate c_k by hand or via a quick Python check (do NOT skip — sign errors here cascade through 14 integral ops). Cross-check `c_0 = 1` and `c_14 = 11778624` before proceeding. A useful quick check: run `python3 -c "import numpy; a=[-1,56,-756,4200,-11550,16632,-12012,3432]; print(numpy.convolve(a,a).tolist())"` to dump all 15 c_k values.

**Lean structure** (mirror cycle 279's n=6 recipe, scaled to 14 ops):

```lean
theorem butcherShiftedLegendre_norm_sq_seven :
    ∫ x in (0:ℝ)..1, (butcherShiftedLegendre 7).eval x ^ 2 = 1 / 15 := by
  have hP : ∀ x : ℝ, (butcherShiftedLegendre 7).eval x ^ 2 =
      c_14 * x^14 + c_13 * x^13 + ... + c_1 * x + c_0 := by
    intro x
    rw [butcherShiftedLegendre_seven]
    simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    ring
  simp_rw [hP]
  -- 14 IntervalIntegrable witnesses (highest-degree to lowest)
  have hi_x14 : IntervalIntegrable (fun x : ℝ => x^14) MeasureTheory.volume 0 1 :=
    (continuous_pow 14).intervalIntegrable 0 1
  -- ... down to hi_x : IntervalIntegrable (fun x : ℝ => x) ...
  -- 14 integral_pow evaluations
  have h14 : ∫ x in (0:ℝ)..1, x^14 = 1/15 := by
    rw [integral_pow]; norm_num
  -- ... down to h1 : ∫₀¹ x = 1/2 ...
  -- Cascade of 14 nested integral_add / integral_sub
  rw [intervalIntegral.integral_add ... ...,
      intervalIntegral.integral_sub ... ...,
      ...]
  rw [intervalIntegral.integral_const_mul, ..., ...]
  rw [h14, h13, ..., h1, intervalIntegral.integral_one]
  ring
```

The opening-paren count on each integrability witness follows the pattern from cycle 279: 13, 12, ..., 1 for the cascading binary ops. Per cycle 279 Discovery #3, n=7 will need 13 opening parens for the outermost witness.

### 1.3 Non-vacuity witness

```lean
example : (1 : ℝ) / (2 * (7 : ℕ) + 1) = 1 / 15 := by norm_num
```

## Priority 2 — Verification & housekeeping

1. `lake env lean OpenMath/Chapter3/Section342.lean` — must exit 0.
2. `lake build OpenMath.Chapter3.Section342` — must succeed.
3. `lake env lean OpenMath/Chapter3.lean` (aggregator) — must exit 0.
4. `grep -c sorry OpenMath/Chapter3/Section342.lean` — must return 0.
5. `#print axioms butcherShiftedLegendre_seven` — must return `[propext, Classical.choice, Quot.sound]`.
6. `#print axioms butcherShiftedLegendre_norm_sq_seven` — same.
7. If Branch A (Aristotle COMPLETE), update `lean_status.json` and `plan.md` to reflect (342d) closure.

## What NOT to try

1. **Do NOT re-poll Aristotle `d4ce527b` more than once.** Single poll per cycle per CLAUDE.md.
2. **Do NOT attempt (342f) three-term recurrence.** Cycle 273 confirmed this requires Pascal-style binomial identities `ring` can't handle, and Mathlib has no standard Legendre infrastructure. Do not retry without (342a) AND substantial new Mathlib hooks.
3. **Do NOT skip the `simp only [coeff_C_mul, coeff_map, coeff_shiftedLegendre]` peel-off before `match`.** Without it, `simp` collapses `C ((-1)^7)` and breaks the coefficient extraction (cycle 277 lesson).
4. **Do NOT use `Polynomial.ext` + `ring` directly.** Cycles 172/173 stalled here for closed-form coefficient identities; the per-coefficient `match k with` pattern from cycles 273–279 is the canonical recipe.
5. **Do NOT attempt `Section441.lean` work.** 43+ consecutive GPFS timeouts since cycle 182. Skip per `cycle_182_gpfs_slowness.md`.
6. **Do NOT skip the c_k convolution sanity check.** Cycle 259's Bell-coefficient miscalculation (cycle 258 task results gave `(1,11,7,26,1)` when correct is `(1,7,4,11,1)`) is the cautionary precedent — hand-verify `c_0`, `c_14`, and at least one mid-index `c_k` before writing the polynomial rewrite.
7. **Do NOT introduce sorries.** Cycle 200/201 rollback precedent: sorry-first scaffolds without a credible single-cycle close get reverted.
8. **Do NOT modify `scripts/autonomous_loop.py`.** Loop-maintainer territory.
9. **Do NOT raise `maxHeartbeats` above 200000.** If the cascaded `integral_add`/`integral_sub` rewrites stall, the issue is missing `IntervalIntegrable` witnesses, not heartbeat exhaustion.
10. **Do NOT introduce `axiom`/`constant` declarations.**

## Risk assessment

- **R1 (LOW)**: `Polynomial.coeff_shiftedLegendre` formula. Verified by cycles 271–279 to hold; same simp recipe ports to n=7. If unexpected behavior, use `mcp__lean-lsp__lean_hover_info` on the symbol.
- **R2 (MEDIUM)**: c_k convolution arithmetic for n=7. 15 coefficients × 8 cross-terms each = 120 multiplications. Use a Python one-liner or Bash `python3 -c "..."` to verify before writing the polynomial rewrite. Sign errors here are the most likely failure mode.
- **R3 (LOW-MEDIUM)**: 14-deep nested `intervalIntegral.integral_add` / `integral_sub` cascade. Cycle 279 confirmed the pattern scales linearly; n=7 adds 2 ops over n=6. Watch the opening-paren counts.
- **R4 (LOW)**: `decide`-helpers `Nat.choose n k = …`. All 11 binomial values for n=7 are small (≤3432), so `decide` will close them in milliseconds.
- **R5 (LOW)**: Section342.lean grows from 1466 → ~1670 LOC. Per cycle 279 Discovery #4, splitting threshold is "after general (342d) lands OR after n=8". Do not split this cycle.

## File size projection

After cycle 280: Section342.lean expected at ~1670 LOC (Branch B, n=7 added) or ~1500-1800 LOC (Branch A, general (342d) replacing or augmenting concrete witnesses). Splitting can wait per cycle 279 Discovery #4.

## Cycle 281+ outlook

- **If Branch A landed**: §342 (342a/b/c/d/e) all closed; only (342f) recurrence and (342g) zeros remain. Pivot to (342g) attempt (orthogonality + Sturm-type arguments) or fresh entity (`lem:342B`, `thm:344A`).
- **If Branch B landed**: continue ladder to n=8 OR pivot to fresh entity. The ladder has diminishing returns; n=8 would push file to ~1900 LOC and is mostly mechanical.
- **File split**: candidates after cycle 280 or 281 are `Section342Basic.lean` (defn + 342b/c/e), `Section342Orthogonality.lean` (342a + IBP helpers), `Section342NormSquare.lean` (342d ladder + general).
