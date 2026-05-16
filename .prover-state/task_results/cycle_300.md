# Cycle 300 Results

## Worked on
- Mandatory single Aristotle poll on project `5939f28b-c890-4b7f-be4f-ed0f31f0d0b5`
  (general (342g): `P_n^*` has `n` distinct real zeros in `(0, 1)`).
- Branch B per the cycle 300 strategy decision table: shipped the
  `n = 13` empirical anchor for clause (342g) of `lem:342A`. Two new
  theorems in `OpenMath/Chapter3/Section342.lean`:
  - `butcherShiftedLegendre_thirteen` — closed-form expansion as a
    `Polynomial ℝ` with coefficients `(±1, ±182, ±8190, …, ±10400600)`.
  - `butcherShiftedLegendre_thirteen_roots` — existential statement of
    thirteen distinct real roots in `Set.Ioo (0 : ℝ) 1`.

## Approach
1. **Aristotle poll** (one only, per CLAUDE.md). Returned `IN_PROGRESS`
   at 30% (created 2026-05-15T22:11:40Z, last update 2026-05-16T00:19:38Z,
   +1pp from cycle 299's 29%). Per the cycle 300 decision table this is
   the "≥ 30%, up" cell → Branch B (ship n=13 anchor, do not cancel).
2. **Python `Fraction` pre-verification** of `P_13^*` at all 14 proposed
   bracket endpoints (plus `1/2`). Confirmed alternating-sign pattern
   `-, +, -, +, -, +, -, 0, +, -, +, -, +, -, +` over
   `0, 1/100, 1/20, 1/10, 1/5, 3/10, 2/5, 1/2, 3/5, 7/10, 4/5, 9/10,
   19/20, 99/100, 1` and validated 13 sign changes (= number of roots,
   one at `1/2` from the parity helper, six in `(0, 2/5)`, six in
   `(3/5, 1)`). Note: the planner's draft grid suggested a 14-bracket
   layout including `(2/5, 9/20)` and `(11/20, 3/5)`, but
   `P_13^*(2/5) < 0` and `P_13^*(9/20) < 0` (no sign change in
   `(2/5, 9/20)`); replaced with 6 + 6 brackets straddling `1/2`.
3. **Closed form**: added `butcherShiftedLegendre_thirteen` immediately
   after the cycle 287 `_eleven` closed form, following the same per-`k`
   `simp` + `norm_num` template with `decide`-evaluated `Nat.choose`
   constants (`Nat.choose 15 13 = 105`, …, `Nat.choose 26 13 = 10400600`).
   Tail case `(k + 14)` uses `Nat.choose_eq_zero_of_lt`.
4. **Roots theorem**: 14 `hf_*` evaluations of `P_13^*` at the bracket
   endpoints (each `rw [hP13]; simp [Polynomial.eval_*]; norm_num`),
   the parity-helper invocation
   `butcherShiftedLegendre_eval_half_eq_zero_of_odd 13 ⟨6, rfl⟩`, twelve
   IVT-based existence calls (six `intermediate_value_Ioo` ascending,
   six `intermediate_value_Ioo'` descending), an explicit
   `clear hP13 hcont hf_*` (retaining `hf_half` + all `hrᵢ_eval` /
   `hrᵢ_mem`) immediately before the `refine`, then 78 distinctness
   blocks + 13 `Ioo (0, 1)` membership goals all closed by
   `intro h; linarith` / `exact ⟨by linarith, by linarith⟩` against the
   bracket endpoints.

## Result
**SUCCESS** — `lake env lean OpenMath/Chapter3/Section342.lean` exits 0
with zero errors (only pre-existing linter warnings on unused simp
arguments in cycle 192-era code; not introduced by cycle 300).
File grew from 5013 → 5747 LOC (+734 LOC).

Axiom check on both new theorems (via `lean_verify`):
- `butcherShiftedLegendre_thirteen`: `[propext, Classical.choice, Quot.sound]`.
- `butcherShiftedLegendre_thirteen_roots`: `[propext, Classical.choice, Quot.sound]`.
No new axioms.

The cycle 299 `clear` mitigation behaved exactly as predicted at this
scale: outer-bracket denominators are `5 × 10²³` (24-digit), which would
have made `linarith`/`isDefEq` preprocessing intractable; the explicit
`clear` block keeps the post-`refine` distinctness goals using only the
small-rational bracket-endpoint facts already extracted into `hrᵢ_mem`.

## Faithfulness check
Both new declarations are *anchors* of the unformalized general (342g)
clause of `lem:342A` (still partial; not promoted in `lean_status.json`
per Branch B housekeeping rule).

### `butcherShiftedLegendre_thirteen` (closed-form lemma — not a textbook entity)
- Entity ID: helper lemma, no JSON entry. Computes
  `butcherShiftedLegendre 13` as an explicit `Polynomial ℝ` expression.
- Lean statement captures: helper for `_thirteen_roots`. Truth value
  follows from `butcherShiftedLegendre_natDegree`-style coefficient
  expansion of the underlying Mathlib `shiftedLegendre 13`.
- Tautology / identity / strength checks: not applicable
  (computational closed form, not a stated lemma in Butcher).

### `butcherShiftedLegendre_thirteen_roots` (empirical anchor — not a textbook entity)
- Entity ID: anchor lemma, no JSON entry. The textbook clause (342g) of
  `lem:342A` is
  > "P_n^* has n distinct real zeros in the open interval (0, 1)."
  (quoted from `extraction/formalization_data/entities/lem_342A.json`,
  property (342g)).
- Lean statement captures: **weaker** than the textbook clause —
  specializes `∀ n` to `n = 13`. Same logical content modulo the
  universal quantifier.
- Justification for divergence: the general (342g) is still open
  (Aristotle in flight at 30%). The empirical ladder
  `n ∈ {1, 3, 5, 7, 9, 11, 13}` (cycles 294–300) provides concrete
  axiom-clean witnesses for downstream use and reduces risk of definition
  smuggling if Aristotle returns an incorrect general proof — each
  specialization can be cross-checked against the corresponding
  empirical anchor.
- Tautology check: conclusion is an existential over thirteen distinct
  roots; not appearing verbatim in any hypothesis. ✓
- Identity check: proof is not `exact h` — uses 12 IVT applications +
  parity helper + 78 distinctness blocks. Real mathematical work. ✓
- Hypothesis strength check: theorem has no hypotheses (concrete `n`
  specialization). ✓
- Absent-theorem check: no comment promises a sorry that doesn't
  exist. ✓

## Dead ends
- The planner's suggested 14-bracket grid (left half ending in
  `(2/5, 9/20)`, right half starting with `(11/20, 3/5)`) does not
  realize sign changes in the inner two brackets — `P_13^*` stays
  negative across `(2/5, 1/2)` and positive across `(1/2, 3/5)` (verified
  by Python `Fraction`). Replaced with 6 left brackets + parity-forced
  `1/2` + 6 right brackets totaling 13 roots, which matches the actual
  sign-change count from a 1/1000-grid scan.

## Discovery
- The cycle 299 `clear hf_*` mitigation generalizes cleanly: for `n = 13`
  the outer-bracket denominators jumped from `5 × 10¹⁶` (n = 11) to
  `5 × 10²³` (a `7e7`-fold increase), yet the post-`refine` distinctness
  block runtime stayed comparable to cycle 299. The `clear` step is
  what protects `linarith` from `isDefEq` scaling on the large-rational
  hypotheses — confirming the cycle 299 hypothesis. Expect the same
  pattern to work at `n = 15` (denominators ≈ `5 × 10²⁹`) and beyond, if
  the empirical ladder is ever extended past the cycle 300 plan's
  recommended stopping point.
- Bracket-grid design heuristic: for odd `n`, use endpoints at uniform
  intervals away from `1/2` with denominators escalating only at the
  outermost two brackets where the root is exponentially close to `0`
  or `1`. For `n = 13` the smallest root is at `x ≈ 0.0075` and the
  outermost bracket `(0, 1/100)` is the only one needing a denominator
  larger than `20`.

## Suggested next approach
Per cycle 300 strategy:
- The planner explicitly warned **do not extend the empirical ladder
  past `n = 13` in cycle 300**, citing diminishing marginal value. Cycle
  301 should therefore re-poll Aristotle `5939f28b` once and branch:
  - `COMPLETE` / `COMPLETE_WITH_ERRORS` → integrate per Branch A / A'.
  - `IN_PROGRESS, ≥ 31%` → healthy; pivot to `lem:342B` (Gaussian
    quadrature exactness degree) or `thm:342C` (order-condition
    equivalence) as a single-cycle viable target *or* continue the
    ladder defensively at `n = 15` (estimated ~700 LOC by linear
    extrapolation of cycles 295–300).
  - `IN_PROGRESS, = 30%` (flat after one growth cycle) → first stall
    observation. Per cycle 285 three-stall protocol, only observe; do
    not cancel.
  - `IN_PROGRESS, < 30%` → second regression observation if it persists.
  - `FAILED` → pivot to manual closure plan (§D of cycle 300 strategy),
    starting with the Phase A.1 sign-change-cardinality lemma.
- The cycle 300 anchor closes the empirical ladder at the planner's
  recommended stopping point. Future planners should weigh
  `lem:342B`/`thm:342C` pivot against ladder-extension; the marginal
  value of `n = 15`/`n = 17` is low unless Aristotle has stalled hard.
