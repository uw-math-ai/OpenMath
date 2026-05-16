# Cycle 319 Strategy

## Headline

Ship **Phase C.1 of `thm:344A`** — small-`s` explicit root theorems
for `butcherRadauI`, `butcherRadauII`, and `butcherLobatto` at `s ∈
{1, 2, 3}` where applicable. Natural next deliverable after cycle
318's Phase B.1 orthogonality theorems; mirrors cycle 294's
empirical-anchor pattern for §342's `(342g)` clause; abscissae-side
prerequisite for the eventual Phase B.2 polynomial-exactness theorem
and Phase D RKTableau construction.

**Goal**: ship five root-witness theorems axiom-clean, ~120 LOC,
sorry count 0 → 0.

## Why this is the right cycle 319 target

The cycle 318 task results suggest two paths:

* **Phase B.2 — polynomial-exactness for Radau I** (the natural
  next conceptual step) — but flags that the `R.natDegree < s`
  contribution "requires Lagrange-interpolation infrastructure at
  the (yet-unconstructed) Radau abscissae". So Phase B.2 needs
  Phase C first.
* **Phase C — small-`s` Radau/Lobatto abscissae** — listed as the
  fallback. This is the right call.

Cycle 317 already shipped the explicit polynomial forms at small
`s` (`butcherRadauI_one`, `butcherRadauI_two`, `butcherRadauII_one`,
`butcherRadauII_two`, `butcherLobatto_two`, `butcherLobatto_three`,
in `Section344.lean` lines 179–270). The roots factor cleanly with
**rational** values — no `Real.sqrt` needed (in contrast to cycle
294's `(3 ± √3)/6` for `butcherShiftedLegendre_two_roots`). Each
root theorem reduces to a `rw` + `simp` + `norm_num` chain.

## Pre-computed root tables

| Polynomial | Closed form (cycle 317) | Factored | Roots |
|---|---|---|---|
| `butcherRadauI 1` | `2X` | `2X` | `x = 0` |
| `butcherRadauI 2` | `6X² − 4X` | `2X(3X − 2)` | `x = 0, 2/3` |
| `butcherRadauII 1` | `2X − 2` | `2(X − 1)` | `x = 1` |
| `butcherRadauII 2` | `6X² − 8X + 2` | `2(3X − 1)(X − 1)` | `x = 1/3, 1` |
| `butcherLobatto 2` | `6X² − 6X` | `6X(X − 1)` | `x = 0, 1` |
| `butcherLobatto 3` | `20X³ − 30X² + 10X` | `10X(2X − 1)(X − 1)` | `x = 0, 1/2, 1` |

All roots are in `[0, 1]`. Radau I has the left endpoint `0`; Radau
II has the right endpoint `1`; Lobatto has both endpoints. Interior
abscissae are `2/3` (Radau I, s=2), `1/3` (Radau II, s=2), `1/2`
(Lobatto, s=3).

## Deliverables (5 P1 theorems + 1 P3 stretch)

Append to `OpenMath/Chapter3/Section344.lean` immediately after
`butcherLobatto_orthogonal_to_lower_degree` (the last cycle-318
theorem, around line 469 of the current 469-LOC file).

### P1.1: `butcherRadauI_one_root`

```lean
theorem butcherRadauI_one_root :
    (butcherRadauI 1).eval (0 : ℝ) = 0 := by
  rw [butcherRadauI_one]
  simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
```

The single root of `butcherRadauI 1 = 2X` is the left endpoint
`x = 0`. Consistent with cycle 317's `butcherRadauI_eval_zero` (a
direct corollary, but worth shipping as a named theorem for
abscissae-table use downstream).

### P1.2: `butcherRadauI_two_roots`

```lean
theorem butcherRadauI_two_roots :
    (butcherRadauI 2).eval (0 : ℝ) = 0 ∧
    (butcherRadauI 2).eval (2/3 : ℝ) = 0 ∧
    (0 : ℝ) ≠ 2/3 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [butcherRadauI_two]
    simp [Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  · rw [butcherRadauI_two]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
               Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  · norm_num
```

Roots of `butcherRadauI 2 = 6X² − 4X` are `x = 0` and `x = 2/3`.

### P1.3: `butcherRadauII_one_root`

```lean
theorem butcherRadauII_one_root :
    (butcherRadauII 1).eval (1 : ℝ) = 0 := by
  rw [butcherRadauII_one]
  simp [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
```

The single root of `butcherRadauII 1 = 2X − 2` is the right
endpoint `x = 1`. Consistent with cycle 317's
`butcherRadauII_eval_one`.

### P1.4: `butcherRadauII_two_roots`

```lean
theorem butcherRadauII_two_roots :
    (butcherRadauII 2).eval (1/3 : ℝ) = 0 ∧
    (butcherRadauII 2).eval (1 : ℝ) = 0 ∧
    (1/3 : ℝ) ≠ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [butcherRadauII_two]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
               Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  · rw [butcherRadauII_two]
    simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  · norm_num
```

Roots of `butcherRadauII 2 = 6X² − 8X + 2` are `x = 1/3` (interior)
and `x = 1` (right endpoint).

### P1.5: `butcherLobatto_two_roots`

```lean
theorem butcherLobatto_two_roots :
    (butcherLobatto 2).eval (0 : ℝ) = 0 ∧
    (butcherLobatto 2).eval (1 : ℝ) = 0 ∧
    (0 : ℝ) ≠ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [butcherLobatto_two]
    simp [Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  · rw [butcherLobatto_two]
    simp [Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  · norm_num
```

Roots of `butcherLobatto 2 = 6X² − 6X` are both endpoints `x = 0`
and `x = 1`.

### P3 stretch: `butcherLobatto_three_roots`

```lean
theorem butcherLobatto_three_roots :
    (butcherLobatto 3).eval (0 : ℝ) = 0 ∧
    (butcherLobatto 3).eval (1/2 : ℝ) = 0 ∧
    (butcherLobatto 3).eval (1 : ℝ) = 0 ∧
    (0 : ℝ) ≠ 1/2 ∧ (0 : ℝ) ≠ 1 ∧ (1/2 : ℝ) ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [butcherLobatto_three]
    simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  · rw [butcherLobatto_three]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
               Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num
  · rw [butcherLobatto_three]
    simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  · norm_num
  · norm_num
  · norm_num
```

Roots of `butcherLobatto 3 = 20X³ − 30X² + 10X` are `x = 0`,
`x = 1/2` (interior), and `x = 1`. Three pairwise-distinct roots.

## LOC budget

* Per theorem (P1.1–P1.5): ~12–25 LOC including docstring (P1.1
  and P1.3 are simplest at ~10 LOC; P1.2/P1.4/P1.5 with multi-root
  conjunctions ~22 LOC).
* P3 stretch: ~35 LOC.
* Target total (P1.1–P1.5): **~110 LOC**.
* With P3 stretch: **~145 LOC**.
* Abort threshold: **200 LOC** (well clear of budget unless
  something pathological surfaces).

## Pre-flight risk register

Mechanical and low-risk, but flag these:

* **R1 (simp set collapse)**: cycle 317's small-`s` polynomial
  forms close via `simp [Polynomial.eval_*] + ring`. Cycle 319
  root proofs close via `simp [Polynomial.eval_*] + norm_num`
  (the goal is `0 = 0` after evaluation, not a polynomial
  identity). **Mitigation**: cycle 294's
  `butcherShiftedLegendre_one_root` at
  `Section342.lean:3699–3707` uses exactly this pattern; works
  cleanly there.
* **R2 (rational-root `norm_num`)**: evaluating at `2/3`, `1/3`,
  `1/2` leaves residuals like `6 * (2/3)^2 - 4 * (2/3) = 0`.
  `norm_num` handles these; if it chokes, fall back to
  `simp; ring_nf; norm_num` or explicit `show (0 : ℝ) = 0; ring`.
* **R3 (distinctness clauses)**: `(0 : ℝ) ≠ 2/3` etc. close
  trivially by `norm_num`. No `linarith` chain needed.
* **R4 (cycle 317 name verification)**: the small-`s` forms are
  named `butcherRadauI_one`, `butcherRadauI_two`,
  `butcherRadauII_one`, `butcherRadauII_two`, `butcherLobatto_two`,
  `butcherLobatto_three`. Verified by `grep` at `Section344.lean`
  lines 179, 193, 207, 221, 237, 252.
* **R5 (`simp` vs `simp only`)**: for the `eval = 0` case after
  rewrite, plain `simp` should close `(0 : ℝ) = 0` directly.
  For the non-zero rational arguments (`2/3`, `1/3`, `1/2`), use
  `simp only [...]` followed by `norm_num` to prevent `simp`
  from over-reducing the rational arithmetic and leaving a stuck
  goal. Both patterns appear in the theorems above.

## What NOT to try

* **Do NOT attempt Phase B.2** (polynomial-exactness for Radau I).
  Per cycle 318 task results, needs Lagrange-interpolation
  infrastructure at Radau abscissae — multi-cycle.
* **Do NOT attempt general-`s` root-counting** for Radau/Lobatto.
  The §342 analog (`butcherShiftedLegendre_n_distinct_real_zeros`,
  cycle 301) required Aristotle integration with sign-change-
  contradiction infrastructure + cycle 292's basis-span lemma.
  Radau/Lobatto is **harder** because the endpoint zeros (0
  and/or 1) must factor out before the sign-change argument
  applies to the residual quotient. Multi-cycle.
* **Do NOT attempt `thm:342C` clauses (342j)/(342k)/(342l)**.
  Blocked on `thm:314A` (elementary-differential independence) per
  plan.md.
* **Do NOT try to compile `OpenMath/Chapter4/Section441.lean`**.
  43+ consecutive GPFS timeouts since cycle 182 (see
  `cycle_182_gpfs_slowness.md`). Skip entirely.
* **Do NOT use `Real.sqrt`**. All cycle 319 roots are rational
  (0, 1/3, 1/2, 2/3, 1). Adding `Real.sqrt` would be pointless
  complication.
* **Do NOT introduce `axiom`, `constant`, or sorries**. Standard
  CLAUDE.md rule + cycles 138/149/200 rollback precedent: if a
  deliverable doesn't close cleanly, ship smaller scope rather
  than leaving sorries.
* **Do NOT raise `maxHeartbeats`**. Proofs are short evaluations;
  if a single `simp` blows past, decompose into named pieces.
* **Do NOT poll Aristotle**. No active jobs relevant to cycle
  319's deliverable.
* **Do NOT modify `scripts/autonomous_loop.py`**. Standing rule
  per CLAUDE.md and `tautology_scanner_false_positives.md`.

## Faithfulness check (mandatory pre-commit)

For each new theorem, apply the CLAUDE.md checklist:

* **Tautology check**: each root theorem has a *non-trivial*
  conclusion (`eval ... = 0`); the proof works by `rw` to expose
  the explicit polynomial form, `simp` to evaluate, `norm_num`
  to close arithmetic. No identity-on-hypothesis patterns.
* **Identity check**: no proof is `exact h`; all proofs do real
  work via `rw [butcherRadauI_one]` etc.
* **Hypothesis strength**: none of the new theorems take
  hypotheses; the small-`s` roots are universal numerical facts.
  Distinctness clauses `(0 : ℝ) ≠ 2/3` are independent numerical
  facts.
* **Definition smuggling**: no new `def`/`structure`/`class`
  introduced — only `theorem`s appending to existing definitions.
* **Textbook match**: Butcher §344 (p. 244) implicitly identifies
  these zeros when constructing the Radau/Lobatto methods, but
  does not enumerate them as a separate "small-`s` table". The
  Lean formalization makes the small-`s` cases explicit as
  scaffolding for the eventual general theorem (analogous to
  cycle 294's empirical anchors for the cycle 301 general-`n`
  (342g) theorem).

## Cycle 319 worker checklist

1. **Read cycle 317's small-`s` forms** at
   `OpenMath/Chapter3/Section344.lean:179–270` to confirm names
   and exact polynomial expressions. The pattern
   `butcherRadauI_one : butcherRadauI 1 = C 2 * X` etc. is the
   load-bearing rewrite for cycle 319's proofs.
2. **Append five (or six with stretch) new theorems** at the end
   of `Section344.lean` after
   `butcherLobatto_orthogonal_to_lower_degree`. Order:
   `butcherRadauI_one_root` → `butcherRadauI_two_roots` →
   `butcherRadauII_one_root` → `butcherRadauII_two_roots` →
   `butcherLobatto_two_roots` → (stretch)
   `butcherLobatto_three_roots`.
3. **Verify each compiles** via
   `lake env lean OpenMath/Chapter3/Section344.lean` after each
   addition (cheap; the file already compiled in cycle 318).
4. **Verify axiom-clean** via
   `lean_verify OpenMath.Chapter3.Section344.butcherRadauI_one_root`
   etc. — expected `[propext, Classical.choice, Quot.sound]`.
5. **Build aggregator** via
   `lake env lean OpenMath/Chapter3.lean` — should be a fast
   rebuild.
6. **Pre-commit faithfulness check** (CLAUDE.md mandatory):
   apply the checklist to each new theorem. No structural issues
   anticipated.
7. **Write `task_results/cycle_319.md`** documenting the five (or
   six) shipped theorems, axiom status, and the cycle 320 entry
   point.
8. **Commit + push** with descriptive message:
   `Cycle 319 — §344 Phase C.1: small-s root theorems for Radau I/II + Lobatto.`

## Cycle 320 entry point (planning hint, do NOT execute)

With Phase C.1 (small-`s` abscissae) shipped, cycle 320 has three
options:

* **(a) Small-`s` Lagrange weights**: ship
  `butcherRadauI`/`butcherRadauII`/`butcherLobatto` small-`s`
  Lagrange-basis weights, mirroring cycle 303's
  `butcherShiftedLegendre_quadratureWeights` definition restricted
  to the small-`s` abscissae from cycle 319. Stepping stone to
  Phase D RKTableau construction.
* **(b) General-`s` Phase C**: attempt the §344 analog of cycle
  301's `butcherShiftedLegendre_n_distinct_real_zeros`.
  **Higher risk**: endpoint-zero factoring requires careful
  bookkeeping. Multi-cycle.
* **(c) Pivot to fresh entity**: e.g., `thm:302C` (Rooted Tree
  Enumeration Formulas) or one of the open §380 entities.

Recommend (a) for cycle 320: it's a clean follow-up that unblocks
small-`s` Phase B.2 (`R.natDegree < s` Lagrange collapse) and
provides RKTableau-side non-vacuity witnesses at `s ∈ {1, 2}` for
Radau I/II and `s ∈ {2, 3}` for Lobatto. Each small-`s` weight
set is ~30 LOC.

## Summary

* **Target**: Phase C.1 of `thm:344A` — small-`s` root theorems
  for Radau I/II and Lobatto.
* **Deliverables**: 5 P1 + 1 P3-stretch axiom-clean theorems in
  `OpenMath/Chapter3/Section344.lean`.
* **LOC budget**: ~110 LOC (P1), ~145 LOC with stretch, abort at
  200 LOC.
* **Risk**: low. Mechanical `rw` + `simp` + `norm_num`; cycle 294
  precedent at §342 confirms the pattern.
* **Faithfulness**: clean. No new definitions, no hypothesis
  divergence, no definition smuggling. Stepping stones for cycle
  320+ Phase B.2 / Phase D work.
* **Sorry count**: 0 → 0 (axiom-clean ship or skip per the
  138/149/200 rollback precedent).
