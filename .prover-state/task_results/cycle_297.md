# Cycle 297 Results

## Worked on

- Single-poll Aristotle project `5939f28b-c890-4b7f-be4f-ed0f31f0d0b5`
  ((342g) general statement). Result: `IN_PROGRESS`,
  `percent_complete = 25` at `2026-05-15T23:19:53Z`. Flat from cycle
  296's 25% — observation #1 of the three-stall protocol; not yet a
  cancel signal.
- Branch C (per cycle 297 strategy decision table): shipped the
  `n = 7` empirical anchor `butcherShiftedLegendre_seven_roots` in
  `OpenMath/Chapter3/Section342.lean`.
- Appended cycle 297 stall observation to
  `.prover-state/issues/lem_342A_g_zeros_scoping.md`.

## Approach

Mechanical scaling of cycle 296's
`butcherShiftedLegendre_five_roots` recipe (lines 3772–3921) to
seven roots. Bracket plan:

| Root | Bracket | IVT direction | Endpoints |
|---|---|---|---|
| r₁ ≈ 0.025 | (0, 1/10) | ascending | `f(0) = -1`, `f(1/10) = 74891/312500` |
| r₂ ≈ 0.129 | (1/10, 1/5) | descending (`Ioo'`) | `f(1/10) = +`, `f(1/5) = -25203/78125` |
| r₃ ≈ 0.297 | (1/5, 2/5) | ascending | `f(1/5) = -`, `f(2/5) = 22931/78125` |
| r₄ = 1/2 | — | parity helper | `f(1/2) = 0` exact |
| r₅ ≈ 0.703 | (3/5, 4/5) | ascending | `f(3/5) = -22931/78125`, `f(4/5) = 25203/78125` |
| r₆ ≈ 0.871 | (4/5, 9/10) | descending (`Ioo'`) | `f(4/5) = +`, `f(9/10) = -74891/312500` |
| r₇ ≈ 0.975 | (9/10, 1) | ascending | `f(9/10) = -`, `f(1) = 1` |

The middle root r₄ = 1/2 is dispatched in one line by cycle 295's
`butcherShiftedLegendre_eval_half_eq_zero_of_odd 7 ⟨3, rfl⟩` (Odd 7
witnessed by 7 = 2·3 + 1).

**Bracket choice deviation from strategy.** The cycle 297 strategy
proposed (0, 1/20), (1/20, 1/5), (1/5, 2/5), (3/5, 4/5), (4/5, 19/20),
(19/20, 1). Computing `P_7^*(1/20) = 58851999/160000000` (a 9-digit
numerator) suggested potential `norm_num` slowness. The cleaner
brackets above use only denominators ≤ 10 and yield evaluations with
≤ 6-digit numerators. Both bracket plans contain exactly one root per
interval (verified against approximate root locations
{0.025, 0.129, 0.297, 0.500, 0.703, 0.871, 0.975}).

Distinctness (21 pairs) is dispatched by `linarith` on the
disjoint-interval chain
`(0, 1/10) < (1/10, 1/5) < (1/5, 2/5) < {1/2} < (3/5, 4/5) <
(4/5, 9/10) < (9/10, 1)`.

Each evaluation `hf_X` is closed by the cycle 296 pattern:
```
rw [hP7]
simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
norm_num
```
`norm_num` closed every evaluation without timeout.

## Result

**SUCCESS.**

- `lake build OpenMath.Chapter3.Section342` exits 0; only pre-existing
  linter warnings (unused simp args at lines 560/643/735/836/946/1091/
  1190/1195/1224/1280/1284/3538) — none in the cycle 297 block
  (3923–4196).
- `#print axioms butcherShiftedLegendre_seven_roots` returns
  `[propext, Classical.choice, Quot.sound]` only.
- Theorem statement asserts: `∃ r₁..r₇ ∈ Ioo 0 1`, all distinct, all
  zeros of `(butcherShiftedLegendre 7).eval`. 21 distinctness
  conjuncts, 7 Ioo memberships, 7 evaluations.
- LOC: 274 (lines 3923–4196 inclusive of the docstring).

## Faithfulness check

For `butcherShiftedLegendre_seven_roots`:

- **Entity ID**: `lem:342A`, clause (342g) at n = 7.
- **Textbook statement** (quoted from
  `extraction/formalization_data/entities/lem_342A.json`,
  `statement_latex` field):
  > `P_n^*` has `n` distinct real zeros in the interval `(0, 1)`,
  > `n = 0, 1, 2, …`. (342g)
- **Lean statement captures**: the n = 7 instance only — strictly
  weaker than (342g)'s ∀-claim. This is an *empirical anchor*
  (continuing the cycle 294/295/296 ladder n=1, 2, 3, 5, 7), not a
  proof of (342g). The general statement is being closed by Aristotle
  project `5939f28b` (still IN_PROGRESS).
- **Justification for not closing the headline**: Aristotle is healthy
  (25% complete, observation #1 of three-stall protocol). Per cycle
  297 strategy §F.1, manual closure of the general (342g) statement
  is forbidden while Aristotle is healthy.

`lean_status.json` for `lem:342A` is **not** updated — the lemma
remains `unformalized` (still `partial` state per prior cycles is
acknowledged via empirical anchors but the entity-level row only
flips to `formalized` when Aristotle closes the general (342g)
statement). The new theorem is a witness for n = 7, not the headline.

No new `def`s, no new `class`/`structure`s, no new helper functions.
The only new theorem is `butcherShiftedLegendre_seven_roots`, an
empirical witness.

## Dead ends

None. The recipe scaled cleanly from n = 5 to n = 7 with no
unexpected `norm_num` failures or IVT direction errors. The bracket
choice (cleaner denominators ≤ 10 instead of the strategy's
denominators 20) was a precautionary move; the strategy's brackets
likely also work.

## Discovery

- The cycle 296 evaluation pattern (`rw [hP_n]; simp [eval_sub, ..., eval_X]; norm_num`)
  scales linearly through n = 5 → 7. For n = 9, where
  `butcherShiftedLegendre_nine` (cycle 285) is a 9-term polynomial
  with coefficient 48620, the same pattern should still close, though
  `norm_num` will see ≤ 7-digit numerators per evaluation.
- Bracket choice has more flexibility than the strategy suggested:
  any disjoint bracket containing only the target root works. For
  n = 7, `{(0, 1/10), (1/10, 1/5), (1/5, 2/5), (3/5, 4/5),
  (4/5, 9/10), (9/10, 1)}` is the natural choice extending cycle
  296's `{(0, 1/10), (1/10, 1/4), (3/4, 9/10), (9/10, 1)}`.
- The cycle 295 parity helper `butcherShiftedLegendre_eval_half_eq_zero_of_odd`
  is now used in three anchors (n=1, 3, 5, 7 — though n=1 predates
  the helper). It will close r_{(n+1)/2} = 1/2 for every odd n in
  one line.

## Suggested next approach

For cycle 298:

1. **Single-poll Aristotle `5939f28b`**. If still IN_PROGRESS at 25%,
   that is observation #2 of the three-stall protocol — still do
   **NOT** cancel.
2. **Branch decision** per cycle 297's table:
   - If COMPLETE: **Branch A** — integrate the proof.
   - If IN_PROGRESS at 25% (obs #2): ship `butcherShiftedLegendre_nine_roots`
     (n = 9 empirical anchor). Cycle 285's
     `butcherShiftedLegendre_nine` provides the closed form
     `P_9^* = 48620X^9 - 218790X^8 + 411840X^7 - 420420X^6
     + 252252X^5 - 90090X^4 + 18480X^3 - 1980X^2 + 90X - 1`. Same
     IVT + parity-helper recipe; ~280 LOC estimated (one more
     ascending+descending pair than n = 7).
   - If COMPLETE_WITH_ERRORS / FAILED: review and either patch +
     resubmit or escalate to manual per the four-phase plan in
     `lem_342A_g_zeros_scoping.md`.
3. **Three-stall trigger**: if cycle 298 observes 25% (obs #2) and
   cycle 299 observes 25% (obs #3), cycle 300 should cancel
   Aristotle and pivot to manual closure.

For cycle 299+ (assuming Aristotle remains stalled but not failed):

- Consider widening the manual-closure groundwork. The full
  contradiction proof requires sign-change extraction (~80 LOC,
  hard) + product-polynomial construction (~40 LOC, easy) +
  integral-positivity (~40 LOC, medium) + orthogonality-contradiction
  closure (~30 LOC). Path B from `lem_342A_g_zeros_scoping.md`
  Branch D should be a four-cycle effort.
- The empirical anchors (n = 1, 2, 3, 5, 7, …) are independently
  useful as test cases for the eventual general proof. If Aristotle
  succeeds, they become redundant (provable by specialisation); if
  Aristotle fails, they are at least named witnesses that downstream
  consumers (e.g. `lem:342B` Gaussian quadrature) can cite at the
  specific n = s of interest for any concrete RK method.
