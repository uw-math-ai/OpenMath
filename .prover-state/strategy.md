# Cycle 278 Strategy

## State summary

Cycle 277 closed **(342a) orthogonality** via Aristotle integration and shipped
the **n = 4 ladder rung** (`butcherShiftedLegendre_four` +
`butcherShiftedLegendre_norm_sq_four`). Section342.lean is now ~1043 LOC,
0 sorries, axiom-clean.

`lem:342A` status (partial):
- (342a) orthogonality ✅ (cycle 277)
- (342b) `P_n^*(1) = 1` ✅ (cycle 271)
- (342c) parity ✅ (cycle 271)
- (342d) norm-square = `1/(2n+1)` — closed at n ∈ {0, 1, 2, 3, 4}; general n
  pending Aristotle `d4ce527b` (last poll: 31%, cycle 277)
- (342e) Rodrigues ✅ (cycle 272)
- (342f) three-term recurrence — NOT started
- (342g) `n` distinct real zeros in `(0, 1)` — NOT started

## Priority 0 — Poll Aristotle `d4ce527b` (single poll, no re-poll)

Run **exactly one** `mcp__aristotle__get_status` call on project
`d4ce527b-b714-4e51-b0a6-e3d06302d7fa` (general (342d) norm-square).

**Branch A — COMPLETE / `success: true`**:
1. `mcp__aristotle__extract_result` to
   `.prover-state/aristotle_results/cycle_278/d4ce527b/`.
2. Read `ARISTOTLE_SUMMARY.md`. Confirm 0 sorries and no axioms beyond
   `[propext, Classical.choice, Quot.sound]`.
3. Integrate the main theorem as
   `butcherShiftedLegendre_norm_sq : ∀ n : ℕ, ∫ x in (0:ℝ)..1,
   (butcherShiftedLegendre n).eval x ^ 2 = 1 / (2 * n + 1)`.
4. Adapt imports as cycle 277 did (likely needs the same Calculus +
   Topology + Tactic.Cases imports already present).
5. Add 3–4 non-vacuity witnesses at small `n` that consume the general
   theorem and reduce to cycle-274/275/276/277's specific instances by
   `norm_num`.
6. Update `lean_status.json` `lem:342A` row: cycle 278, status
   `partial` (still missing (342f), (342g)).
7. **DO NOT** also do the Priority 1 ladder work — Aristotle integration
   was the cycle's substantive deliverable.

**Branch B — IN_PROGRESS / FAILED / COMPLETE_WITH_ERRORS** (most likely
outcome at ~10%/cycle pace, expecting ~40% at this poll):
1. Do **NOT** cancel the project.
2. Proceed to Priority 1 ladder work below.

**Branch C — single poll only**: do not re-poll mid-cycle. If
IN_PROGRESS at the start, treat as a miss for this cycle.

## Priority 1 — Ship n = 5 ladder rung (executed only in Branch B)

Ship two new public theorems in `OpenMath/Chapter3/Section342.lean`,
inserted immediately after `butcherShiftedLegendre_norm_sq_four`.

### 1a. `butcherShiftedLegendre_five`

**Coefficient determination**: do NOT commit to a closed form before
checking with `lean_multi_attempt`. The pattern from cycles 275/276/277:

  - cycle 275 `_two`: `6X² - 6X + 1` (n=2 even, leading positive, constant `+1`).
  - cycle 276 `_three`: `20X³ - 30X² + 12X - 1` (n=3 odd, leading positive, constant `-1`).
  - cycle 277 `_four`: `70X⁴ - 140X³ + 90X² - 20X + 1` (n=4 even, constant `+1`).
  - Pattern: leading coefficient `Nat.choose (2n) n` (always positive);
    constant term `(-1)^n`.

**Probable n=5 closed form** (constant `(-1)^5 = -1`, leading `Nat.choose 10 5 = 252`):

```
P_5^*(x) = 252·x⁵ - 630·x⁴ + 560·x³ - 210·x² + 30·x - 1
```

Sanity at `x = 1`: `252 − 630 + 560 − 210 + 30 − 1 = 1` ✓ (matches
`butcherShiftedLegendre_eval_one`).

Sanity at `x = 0`: constant term `-1 = (-1)^5` ✓ (matches
`butcherShiftedLegendre_eval_zero`).

**Proof recipe** (cycle-276 `_three` template, mechanically extended to
k ∈ {0,1,2,3,4,5,k+6}):

```lean
theorem butcherShiftedLegendre_five :
    butcherShiftedLegendre 5
      = C 252 * X^5 - C 630 * X^4 + C 560 * X^3
        - C 210 * X^2 + C 30 * X - C 1 := by
  unfold butcherShiftedLegendre
  simp only [coeff_C_mul, coeff_map, coeff_shiftedLegendre]
  ext k
  match k with
  | 0 => simp; norm_num
  | 1 => simp; norm_num
  | 2 => simp; norm_num
  | 3 => simp; norm_num
  | 4 => simp; norm_num
  | 5 => simp; norm_num
  | k + 6 => simp [Nat.choose_eq_zero_of_lt (by omega : 5 < k + 6)]
```

The `simp only [coeff_C_mul, coeff_map, coeff_shiftedLegendre]; ext k`
peel-off pattern is **mandatory at all n ≥ 3** per cycle 277 dead-end
discovery. Do NOT try the bare-simp shortcut (cycle 277 confirmed it
fails at n=4 and will fail at n=5).

Per-k arms may need explicit `Nat.choose i j = …` decide-hints (cycle
277 found `Nat.choose 4 2 = 6` needed an explicit decide-helper at
n=4, k=2). Discover stuck arms with `lean_multi_attempt` and patch
inline.

### 1b. `butcherShiftedLegendre_norm_sq_five`

```
∫ x in (0:ℝ)..1, (butcherShiftedLegendre 5).eval x ^ 2 = 1 / 11
```

**Proof recipe** (cycle-277 `_four` template scaled to degree-10
integrand).

1. Expand `(P_5^*(x))^2` as a degree-10 polynomial in `x`. Compute
   coefficients by convolution of `(a_0, ..., a_5) = (-1, 30, -210,
   560, -630, 252)` with itself:
   - `c_k = Σ_{i+j=k} a_i · a_j` for `k ∈ {0, ..., 10}`.
   - Hand-check at minimum the constant (`c_0 = (-1)^2 = 1`) and
     leading (`c_10 = 252^2 = 63504`) terms before committing the
     full expansion.

2. Reduce the integrand pointwise via `eval_pow` + `eval_sub` +
   `eval_add` + `eval_mul` + `eval_X` + `ring`:
   ```
   (P_5^*(x))^2 = c_10·x^10 + … + c_0
   ```

3. Split the integral via 9 nested `intervalIntegral.integral_add` /
   `integral_sub` + `integral_const_mul` × 10. Close each
   `IntervalIntegrable` side-goal with
   `(Polynomial.continuous _).intervalIntegrable _ _` or
   `Continuous.intervalIntegrable`.

4. Each `∫₀¹ x^k` closes with `integral_pow` (k ∈ {1..10}) or
   `integral_one` (k = 0).

5. `ring` / `norm_num` collapses the final arithmetic to `1/11`.

**Verification**: cycle 277's `_norm_sq_four` proof in the file is the
direct template. The expansion grows ≈ 50 LOC per ladder rung.

## Priority 2 (conditional stretch — only if P0=Branch B and P1 ships cleanly with ≥50% cycle budget remaining)

Attempt **(342f) three-term recurrence**:

```
∀ n : ℕ, (n + 1) · P_{n+1}^*(x) = (2n+1) · (2x-1) · P_n^*(x) - n · P_{n-1}^*(x)
```

**Why this is newly tractable**: cycle 273 confirmed `ring` /
per-coefficient routes fail because Pascal-binomial identities are
required. But cycle 277's orthogonality opens the inner-product
expansion route:

1. `x · P_n^*(x)` has degree `n+1`, so lies in
   `span_ℝ {P_0^*, P_1^*, ..., P_{n+1}^*}`.
2. Expand `x · P_n^* = Σ_{k=0..n+1} c_{n,k} · P_k^*`.
3. By cycle 277's orthogonality and the inner-product formula
   `c_{n,k} = ⟨x P_n^*, P_k^*⟩ / ⟨P_k^*, P_k^*⟩`, only `c_{n,n-1}`,
   `c_{n,n}`, `c_{n,n+1}` are nonzero (since
   `⟨x P_n^*, P_k^*⟩ = ⟨P_n^*, x P_k^*⟩` and `x P_k^*` has degree
   `k+1 < n` for `k < n-1`).
4. The three-term shape is then forced. Specific scalar coefficients
   come from `P_n^*(1) = 1` normalization and (342d) norm-squares.

**Time-box and abort condition**: this is genuinely ≥ 200 LOC and may
exceed budget. If you start P2 and stall after **30 minutes of focused
work**, abort, document approach in task results, defer to cycle 279+.
**DO NOT** introduce sorries.

## Priority 3 (do NOT attempt this cycle)

**(342g) `n` distinct real zeros in `(0, 1)`** would require either (a)
Mathlib's general orthogonal-polynomial root theorem or (b) a custom
sign-change argument. Multi-cycle. **Defer.**

## What NOT to try

1. **Do NOT cancel Aristotle project `d4ce527b`** — keep it running
   even if this cycle's poll returns IN_PROGRESS.
2. **Do NOT re-poll Aristotle** — single poll per cycle per CLAUDE.md.
3. **Do NOT use the bare-simp / cycle-275 even-n shortcut for
   `butcherShiftedLegendre_five`**. Cycle 277 confirmed the cycle-276
   peel-off pattern (`simp only [coeff_C_mul, coeff_map,
   coeff_shiftedLegendre]` prepended to `ext k`) is **mandatory at all
   n ≥ 3**.
4. **Do NOT submit a fresh Aristotle job for (342f) recurrence** — the
   cycle-273 attempt established this needs Pascal-binomial machinery
   beyond `ring`'s reach. The inner-product expansion route (P2) is
   the correct fallback.
5. **Do NOT attempt (342g) zeros this cycle** — defer.
6. **Do NOT raise `maxHeartbeats` above 200000**. If a per-k arm of
   `butcherShiftedLegendre_five` stalls, isolate via
   `lean_multi_attempt` and decompose with explicit `Nat.choose`
   decide-helpers.
7. **Do NOT introduce `axiom` or `constant` declarations.**
8. **Do NOT pivot to a different entity this cycle.** The §342 ladder
   has momentum — finish n=5 (or general n via Aristotle) before
   considering other entries.
9. **Do NOT commit a closed form for `butcherShiftedLegendre_five`
   without verifying coefficients via `lean_multi_attempt`** at one or
   two arms first. The hand-computed values above are an educated
   guess based on the n=2/3/4 pattern, not a proof.

## Pre-commit faithfulness checklist (mandatory)

For each new theorem introduced (likely:
`butcherShiftedLegendre_five`, `butcherShiftedLegendre_norm_sq_five`,
and possibly `butcherShiftedLegendre_norm_sq` from Aristotle):

- **`butcherShiftedLegendre_norm_sq_five`**: textbook statement at
  `extraction/raw_text/ch03.txt` §342 (342d):
  > `∫₀¹ P_n^*(x)^2 dx = 1/(2n + 1)`
  At n=5: `1/11`. Lean statement captures **same content** at the
  specific instance.
- **`butcherShiftedLegendre_five`**: this is **helper infrastructure**,
  not a textbook-named entity (cycle 273/275/276/277 precedent).
- **Definition smuggling check**: `butcherShiftedLegendre` is defined
  cycle 271 via Mathlib's `shiftedLegendre n` mapped to ℝ. NOT
  smuggling — orthogonality and norm-squares are proved properties,
  not bakings-in.
- **Tautology check**: each new theorem's conclusion is a non-trivial
  arithmetic / integral / polynomial identity, not a hypothesis
  re-export.
- **Hypothesis strength**: theorems take no IVP-style hypotheses;
  only the implicit polynomial-ring / measure structure from Mathlib.
- **Identity check**: proof bodies do real work (per-coefficient
  `coeff_shiftedLegendre` for `_five`; nested
  `integral_add`/`sub`/`const_mul` + `integral_pow` for `_norm_sq_five`).
  Not `exact h`.

## Build sanity (mandatory before commit)

Run all four:
1. `lake env lean OpenMath/Chapter3/Section342.lean` — must exit 0.
2. `grep -c sorry OpenMath/Chapter3/Section342.lean` — must be `0`.
3. `#print axioms OpenMath.Chapter3.Section342.butcherShiftedLegendre_norm_sq_five`
   (and for each new theorem) — must return
   `[propext, Classical.choice, Quot.sound]` only.
4. `lake env lean OpenMath/Chapter3.lean` — must exit 0 (aggregator
   downstream check).

## State-file updates (mandatory)

1. `extraction/formalization_data/lean_status.json` `lem:342A` row:
   bump `cycle` to 278; `formalization_status` stays `partial` (still
   missing (342f), (342g) in either branch).
2. `plan.md` `lem:342A` row: append cycle 278 marker / note in the
   long-form documentation paragraph.

## Task results format (mandatory)

Write `.prover-state/task_results/cycle_278.md` with:
- **Worked on**: poll result + ladder rung(s) shipped.
- **Approach**: per-section recipe used (which branch, which template).
- **Result**: SUCCESS/FAILED per deliverable.
- **Faithfulness check**: per new theorem.
- **Dead ends**: any approaches that failed (e.g. if `Nat.choose`
  decide helpers needed adjustment, document the specific arm and
  helper used).
- **Discovery**: anything new about the §342 ladder, the peel-off
  pattern, or Aristotle project `d4ce527b`'s progress trajectory
  (note current %, growth rate vs cycle 277).
- **Suggested next approach**: cycle 279 — based on this cycle's
  outcome, pick from {Aristotle integration if still pending, n=6
  ladder rung, (342f) recurrence attempt, pivot to a fresh entity if
  Aristotle has clearly stalled}.

## Commit message template

Choose one based on outcome:

* Branch A (Aristotle integration): `Cycle 278 — §342 (342d) general
  norm-square from Aristotle SHIPPED.`
* Branch B + P1 ships: `Cycle 278 — §342 (342d) n=5 ladder rung SHIPPED.`
* Branch B + P1 + P2 ships (unlikely): `Cycle 278 — §342 (342d) n=5
  ladder rung + (342f) recurrence SHIPPED.`
