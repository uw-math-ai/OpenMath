# Cycle 283 Strategy

## Context (where we are)

Cycle 282 SHIPPED axiom-clean: three concrete `(342f)` three-term
recurrence witnesses for `lem:342A` at `n ∈ {2, 3, 4}` in
`OpenMath/Chapter3/Section342.lean` (LOC 1871 → ~1949, 0 sorries),
plus an Aristotle fire-and-forget submission for the **general**
(342f) recurrence:

- **Aristotle project**: `c8b8f138-f875-4263-94ec-74533b5120d7`
- Submission file: `.prover-state/aristotle_submissions/cycle_282/342f_recurrence.lean`
- Cites cycles 271–281's results as axioms (definition + `eval_one`,
  `eval_one_sub`, `eval_zero`, `natDegree`, `rodrigues`,
  `orthogonal`, `norm_sq`, plus explicit `_zero` through `_four`
  forms).
- Status on submission: QUEUED. Not polled in cycle 282.

Section342.lean state at HEAD:
- 0 sorries, all axiom-clean (`[propext, Classical.choice, Quot.sound]`).
- (342b), (342c), (342a), (342d), (342e) all CLOSED.
- (342f) general OPEN; (342f) at n=2,3,4 CLOSED. (342g) OPEN; scoping
  doc at `.prover-state/issues/lem_342A_g_zeros_scoping.md`.

`lem:342A` row in `plan.md` is `[~]` (partial). It moves to `[x]`
when (342a–g) all close.

## P0 — Aristotle single-poll (5 min, MANDATORY first action)

Call `mcp__aristotle__get_status` ONCE on project
`c8b8f138-f875-4263-94ec-74533b5120d7`. Branch based on status:

### Branch A — COMPLETE

Per CLAUDE.md "Aristotle-first" and cycle 281's `d4ce527b` integration
template:

1. Download the result via `mcp__aristotle__download_result`.
2. Extract the proof body and any helper lemmas Aristotle introduced.
3. Audit for new private/helper machinery. If Aristotle ships
   significant new helper infrastructure (the textbook proof needs a
   leading-coefficient identity `n · C(2n,n) = 2(2n−1) · C(2n−2, n−1)`
   plus an `xP_{n−1}^* = aP_n^* + bP_{n−1}^* + cP_{n−2}^*` style
   expansion via inner-product expansion), consider extracting it to
   a new dedicated file `OpenMath/Chapter3/Section342RecurrenceHelpers.lean`
   mirroring cycle 281's `Section342NormSqHelpers.lean` structure.
   Otherwise inline.
4. Integrate into `OpenMath/Chapter3/Section342.lean` as
   `butcherShiftedLegendre_recurrence (n : ℕ) (hn : 2 ≤ n) : …`.
5. Verify the cycle 282 concrete witnesses
   (`_recurrence_two/three/four`) remain consistent with the general
   form. They may become redundant — leave them in as numerical
   witnesses unless they fail to compile.
6. Run `lake env lean OpenMath/Chapter3/Section342.lean` (and
   `OpenMath/Chapter3.lean` if new file added).
7. `#print axioms` on the new general theorem — must be
   `[propext, Classical.choice, Quot.sound]` only.
8. Update `lem:342A` cycle in `lean_status.json` to 283.
9. If COMPLETE, also as P3: **fire (342g) on Aristotle**. Create
   `.prover-state/aristotle_submissions/cycle_283/342g_distinct_zeros.lean`
   citing all of (342a–f) as available axioms; sketch the proof
   recipe (sign-change contradiction with product polynomial
   `Q := ∏ (X − xᵢ)`); submit. Single fire-and-forget.

### Branch B — IN_PROGRESS (any %) or QUEUED

Per cycle 282 strategy fallback: continue the recurrence-witness
ladder. Aristotle's d4ce527b precedent (cycle 274–281) showed
~14 cycles between submission and completion with ~5%/cycle growth;
expect general (342f) similar.

**Ship `butcherShiftedLegendre_recurrence_five`** at `n = 5`:

```
(5 : ℝ) • P_5^* = C 9 · (C 2 · X − C 1) · P_4^* − C 4 · P_3^*
```

Recipe (cycle 282's `Polynomial.funext + ring` template, verified to
work first-try at n=2,3,4):

```lean
theorem butcherShiftedLegendre_recurrence_five :
    (5 : ℝ) • butcherShiftedLegendre 5 =
      Polynomial.C 9 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 4
      - Polynomial.C 4 * butcherShiftedLegendre 3 := by
  apply Polynomial.funext
  intro x
  rw [butcherShiftedLegendre_five, butcherShiftedLegendre_four,
      butcherShiftedLegendre_three]
  simp [Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one, smul_eq_mul]
  ring
```

Sanity-check the coefficients numerically before writing the proof:
- LHS at `n = 5`: `5 · (252x⁵ − 630x⁴ + 560x³ − 210x² + 30x − 1) =
  1260x⁵ − 3150x⁴ + 2800x³ − 1050x² + 150x − 5`.
- RHS at `n = 5`: `9 · (2x − 1) · (70x⁴ − 140x³ + 90x² − 20x + 1) −
  4 · (20x³ − 30x² + 12x − 1)`.
  - `(2x−1)(70x⁴ − 140x³ + 90x² − 20x + 1)
     = 140x⁵ − 350x⁴ + 320x³ − 130x² + 22x − 1`.
  - `· 9 = 1260x⁵ − 3150x⁴ + 2880x³ − 1170x² + 198x − 9`.
  - Subtract `4(20x³ − 30x² + 12x − 1) = 80x³ − 120x² + 48x − 4`:
    `1260x⁵ − 3150x⁴ + 2800x³ − 1050x² + 150x − 5`. ✓ Matches LHS.

Optionally also ship `_recurrence_six` and `_recurrence_seven` if
time allows — same recipe with cycles 279–280's explicit forms
`_six` and `_seven` already in hand. Each adds ~10–15 LOC.

LOC budget: ~20–60 LOC depending on how many rungs ship.

### Branch C — FAILED / CANCELLED / unexpected

Per cycle 151's precedent (Aristotle general-`n` thm:550A cancelled
at 21%): cancel the project and pivot to manual stepping stones.
Ship `_recurrence_five` per Branch B; pivot future cycles to
`lem:342B` (Gaussian quadrature exactness) which can now consume
(342a–e) plus the (342f) numerical witnesses.

## What NOT to try

- **NEVER** attempt the general `(342f)` proof manually via
  `Polynomial.ext` or `Polynomial.funext + ring`. Cycle 273 confirmed
  this requires Pascal-style binomial identities (`n · C(2n,n) =
  2(2n−1) · C(2n−2, n−1)`) plus inner-product expansion of `xP_{n−1}^*`
  against the basis `{P_k^*}_{k=0..n+1}`. `ring` alone cannot close
  these. The structural proof requires either Aristotle or building
  the standard Bonnet recurrence infrastructure — both multi-cycle
  manually. Stick with Aristotle delegation.

- **NEVER** attempt to compile `OpenMath/Chapter4/Section441.lean`
  on this GPFS. 43+ consecutive timeouts since cycle 182 (per
  `.prover-state/issues/cycle_182_gpfs_slowness.md`). Skip §441 work
  entirely.

- **NEVER** introduce a `sorry`-first scaffold for the general
  (342f) — cycles 200/201 rolled back sorry-first scaffolds; cycles
  149/150 also rolled back; cycles 138/139 also rolled back. Pattern
  is well-established: sorry count rises ⇒ supervisor penalty ⇒
  rollback. Ship axiom-clean or ship recurrence-witness ladder rungs.

- **NEVER** poll Aristotle more than once per cycle. Per CLAUDE.md:
  "Do not poll repeatedly — one check after 30 min is enough." If
  status is QUEUED or low-% IN_PROGRESS, that is the expected state;
  proceed to Branch B without complaint.

- Do **NOT** rename anything in Section342.lean to dodge the
  tautology scanner — past supervisor false-positive scoring (cycles
  243–247) is loop-maintainer territory per
  `.prover-state/issues/tautology_scanner_false_positives.md`.

- Do **NOT** raise `maxHeartbeats`. If a proof stalls, decompose
  it (cycle 281's `Section342NormSqHelpers.lean` extraction precedent).

## P3 (stretch, only if Aristotle COMPLETE and integration finished in <60 min budget)

Fire `(342g)` on Aristotle: distinct real zeros of `P_n^*` in `(0, 1)`.

Per `.prover-state/issues/lem_342A_g_zeros_scoping.md`:
- Use cycle 282's scoping doc as the basis for the prompt.
- Cite (342a)/(342d)/(342e)/(342f) as axioms in the submission.
- LOC budget for the prompt's stub statement: ~30 LOC.
- This is fire-and-forget; do not poll this cycle.

## Deliverables checklist

Minimum (always — Branch A, B, or C):
- [ ] Aristotle `c8b8f138` polled exactly once.
- [ ] If Branch A: general `butcherShiftedLegendre_recurrence` shipped
      and integrated; cycle 282's three concrete witnesses retained
      or audited for consistency.
- [ ] If Branch B: `butcherShiftedLegendre_recurrence_five` shipped
      axiom-clean.
- [ ] If Branch C: `_recurrence_five` shipped (same as B); Aristotle
      project cancelled.

Both branches require:
- [ ] `lake env lean OpenMath/Chapter3/Section342.lean` exits 0.
- [ ] `lake env lean OpenMath/Chapter3.lean` exits 0 (chapter
      aggregator).
- [ ] `grep -c sorry OpenMath/Chapter3/Section342.lean` returns 0.
- [ ] `#print axioms` on each new theorem returns
      `[propext, Classical.choice, Quot.sound]` only.
- [ ] `lean_status.json` `lem:342A` row's cycle bumped to 283.
- [ ] `plan.md` `lem:342A` row updated with cycle 283 closure note
      (still `[~]` partial — (342g) remains).
- [ ] Cycle 283 task results file written to
      `.prover-state/task_results/cycle_283.md`.

Branch A only:
- [ ] (P3 stretch if budget allows) Aristotle (342g) submitted.

## Pre-commit faithfulness check

For each new public theorem (general `butcherShiftedLegendre_recurrence`
or any new `_recurrence_n` rung):

- [ ] Quote the textbook statement from
      `extraction/formalization_data/entities/lem_342A.json`:
      `n P_n^*(x) = (2x − 1)(2n − 1) P_{n−1}^*(x) − (n − 1) P_{n−2}^*(x)`.
- [ ] Confirm the Lean type matches the textbook for the chosen `n`
      (or generally if Branch A).
- [ ] Tautology check: no hypothesis equals the conclusion.
- [ ] Hypothesis strength: minimal (no extra typeclasses or bounds
      beyond `n ≥ 2`).
- [ ] No definition smuggling: this is a theorem witnessing the
      textbook formula, not a redefinition.

## Cycle 284+ outlook

- If Branch A completed: cycle 284 polls Aristotle (342g). If (342g)
  closes, `lem:342A` becomes fully formalized (move `[~]` → `[x]`).
  Then pivot to `lem:342B` (Gaussian quadrature exactness) which
  consumes (342a)–(342g) as inputs.
- If Branch B continuing: cycle 284 polls Aristotle (342f) again,
  extends ladder to `n = 6` if still IN_PROGRESS. Continue until
  Aristotle completes or the ladder runs out (Section342.lean would
  be growing >2500 LOC at n ≥ 10; consider splitting into
  `Section342Ladder.lean` if it crosses 3000 LOC).
- Always: monitor compile time. Cycle 281 used ~14 cycles for
  Aristotle on (342d); pattern expected here.
