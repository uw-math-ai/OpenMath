# Cycle 298 Results

## Worked on

* Aristotle single-poll of project `5939f28b-c890-4b7f-be4f-ed0f31f0d0b5`
  (general (342g) statement).
* `butcherShiftedLegendre_nine_roots` — empirical anchor at `n = 9`
  for clause (342g) of `lem:342A`. Mechanical extension of cycle 297's
  `n = 7` recipe.
* Issue file update at
  `.prover-state/issues/lem_342A_g_zeros_scoping.md` (cycle 298 entry).

## Approach

### Aristotle poll (P1, ~2 min)

Single call to `mcp__aristotle__get_status`. Result:

| field | value |
|---|---|
| status | `IN_PROGRESS` |
| percent_complete | `28` |
| last_updated_at | `2026-05-15T23:38:59Z` |
| previous (cycle 297) | `25` |

Delta `+3 pp` from cycle 297. Strategy branch table: `> 25 %` ⇒
healthy progress, **stall counter resets**, Branch B fires. Cycle 297's
`observation #1` is invalidated by this growth; cycle 299 starts a
fresh three-stall window if 28% holds flat.

### n = 9 anchor (P2 / Branch B, ~90 min)

1. **Bracket sanity-check** via Python `Fraction` exact arithmetic on
   the closed form
   `P_9^* = 48620X^9 − 218790X^8 + 411840X^7 − 420420X^6 + 252252X^5
            − 90090X^4 + 18480X^3 − 1980X^2 + 90X − 1`
   (cycle 285's `butcherShiftedLegendre_nine`). Evaluated at
   `{0, 1/20, 1/8, 1/4, 2/5, 1/2, 3/5, 3/4, 7/8, 19/20, 1}`:

   | x | P_9^*(x) | sign |
   |---|---|---|
   | 0 | −1 | − |
   | 1/20 | 9459468441/25600000000 | + |
   | 1/8 | −(10413009/33554432) | − |
   | 1/4 | 17557/65536 | + |
   | 2/5 | −(96077/390625) | − |
   | 1/2 | 0 | parity |
   | 3/5 | 96077/390625 | + |
   | 3/4 | −(17557/65536) | − |
   | 7/8 | 10413009/33554432 | + |
   | 19/20 | −(9459468441/25600000000) | − |
   | 1 | 1 | + |

   All eight non-parity adjacent pairs sign-flip — bracket plan valid.

2. **Direction-vs-strategy-table discrepancy noted**. The strategy's
   right-half "Direction" column was off-by-parity (claimed all
   ascending for r₆, r₇, r₈, r₉ as "parity-symmetric to" left roots,
   but `P_9^*(1 − x) = -P_9^*(x)` flips direction). Used the
   Python-verified directions instead:
   * `(0, 1/20)` ascending → `intermediate_value_Ioo`
   * `(1/20, 1/8)` descending → `intermediate_value_Ioo'`
   * `(1/8, 1/4)` ascending
   * `(1/4, 2/5)` descending
   * `1/2` parity helper
   * `(3/5, 3/4)` descending
   * `(3/4, 7/8)` ascending
   * `(7/8, 19/20)` descending
   * `(19/20, 1)` ascending

3. **Lean proof** appended to
   `OpenMath/Chapter3/Section342.lean` (lines 4198–4540, ~340 LOC).
   Structure verbatim port of `butcherShiftedLegendre_seven_roots`:
   * Ten `have hf_<endpoint>` evaluations via
     `rw [butcherShiftedLegendre_nine]; simp [...eval_*]; norm_num`.
   * Eight IVT applications + one parity application
     (`butcherShiftedLegendre_eval_half_eq_zero_of_odd 9 ⟨4, rfl⟩`).
   * Single `refine` packing the nine witnesses and 36 + 9 + 9 = 54
     conjuncts.
   * 36 distinctness goals via `obtain ⟨_, hr_lt⟩; obtain ⟨hr_gt, _⟩;
     intro h; linarith`.
   * 9 `Set.Ioo (0:ℝ) 1` goals via `linarith` on bracket endpoints.

4. **Build verification**: `lake env lean OpenMath/Chapter3/Section342.lean`
   exit 0, 29.5 s wall. Then `lake build OpenMath.Chapter3.Section342`
   to refresh oleans (27.5 s). `#print axioms` returns
   `[propext, Classical.choice, Quot.sound]` — axiom-clean.

## Result

**SUCCESS.**

* `butcherShiftedLegendre_nine_roots` axiom-clean, 0 sorries.
* No `maxHeartbeats` increase needed.
* No new definitions.
* Existing n=1, 3, 5, 7 anchors and all (342a)–(342f) theorems
  unaffected.

## Faithfulness check

For the single new theorem this cycle:

**Entity ID and textbook statement** (`lem:342A` clause (342g),
Butcher §342 p. 236):

> `P_n^*` has `n` distinct real zeros in the interval `(0, 1)`,
> and we shall denote them by `ξ_1, ξ_2, …, ξ_n`.

**Theorem `butcherShiftedLegendre_nine_roots`**:

* Lean statement captures: **strictly weaker** (empirical anchor at
  `n = 9`, not the ∀-claim over all `n`).
* Justification for divergence: cycle 294's strategy and §342 of
  `.prover-state/strategy.md` for cycle 298 both explicitly designate
  the n-by-n anchors as a hedge while Aristotle works the general
  case. The cycle 298 strategy states: *"Do NOT bump `lean_status.json`
  row for `lem:342A` to `formalized`. State remains `partial` until
  Aristotle (or manual closure) lands the general statement."*
  No status row was bumped; `plan.md` unchanged.
* Tautology check: no hypothesis is reused as conclusion (the theorem
  has zero hypotheses; conclusion is an existential).
* Identity check: proof is 340 LOC of IVT + parity + linarith — not
  an `exact h` reshuffle.
* Definition smuggling: no new `def`/`structure`. Uses only existing
  `butcherShiftedLegendre`, `butcherShiftedLegendre_nine`,
  `butcherShiftedLegendre_eval_half_eq_zero_of_odd`.
* Hypothesis strength: zero hypotheses (closed statement about a
  concrete polynomial).

No `class`/`structure` introduced this cycle.

## Dead ends

None. The cycle 297 recipe ported cleanly. The pre-verification step
caught the strategy table's parity-flip direction error on the right
half, but this surfaced *before* writing any Lean — only the strategy
narrative needed adjustment, not the proof.

## Discovery

* **`P_9^*` outer-root brackets are tight but `1/20` and `19/20` still
  work**. The strategy flagged risk that denominator 20 might be too
  coarse for outer roots ≈ 0.0159 and 0.9841; in practice the sign
  margin is small (~3.7×10⁻¹) but non-zero, so the IVT brackets
  succeed without needing denominator 100. Recorded here in case
  `n = 11` later needs finer outer brackets.
* **`norm_num` handles 11-digit fractional coefficients comfortably**.
  Each `hf_<endpoint>` evaluation completes in well under a second
  with no `maxHeartbeats` pressure — no need to split coefficients
  into named `have` binds as the strategy contingency suggested.
* **Strategy table directions can be wrong on parity-symmetric pairs**.
  For odd `n`, `P_n^*(1 − x) = -P_n^*(x)` flips sign, so a left bracket
  that's ascending maps to a right bracket that's descending — the
  cycle 298 strategy table got this wrong on r₆–r₉. Pre-computing
  endpoint signs caught it.

## Suggested next approach

For cycle 299:

1. **Single-poll Aristotle `5939f28b` again.** Three outcomes:
   * Healthy growth (`> 28%`): Branch B again (n = 11 anchor) and
     reset stall counter.
   * Flat (`= 28%`): observation #1 of a fresh three-stall window.
     Still Branch B (n = 11).
   * `COMPLETE` / `COMPLETE_WITH_ERRORS` / `FAILED`: dispatch to
     Branch A / C / D per the strategy.
2. **If Branch B fires, ship `butcherShiftedLegendre_eleven_roots`**.
   Needs cycle 287's closed form `butcherShiftedLegendre_eleven`
   (verify it exists at HEAD), the parity helper applied to `⟨5, rfl⟩`
   (since `11 = 2·5 + 1`), and ten IVT brackets. Approximate root
   locations on `[0, 1]` for n=11: ≈ {0.0109, 0.0565, 0.1342, 0.2407,
   0.3631, 0.5, 0.6369, 0.7593, 0.8658, 0.9435, 0.9891}. Outer roots
   are tighter than n=9 — may need denominator 100 for the outermost
   pair `(0, 1/100)` and `(99/100, 1)`. **Pre-verify all 10 bracket
   endpoint signs with Python `Fraction` before writing Lean.**
3. **Coefficient size warning for n = 11**. `P_11^*` leading
   coefficient is 705432 (vs. 48620 for n=9). The `norm_num`
   evaluation should still work but watch for any single evaluation
   taking >10 s — at which point split into named `have` binds.
4. **Spec-side prep**: as the n-by-n stack grows, a uniform
   `butcherShiftedLegendre_has_n_distinct_zeros_in_unit_interval`
   wrapper (parameterized over `n`) could consolidate the anchors —
   defer until Aristotle's general theorem either lands or is
   formally cancelled. Premature abstraction otherwise.
5. **Do not initiate manual closure of general (342g)** until cycle
   300 at earliest (per the cycle 297 strategy §F.1 and the
   three-stall protocol). Aristotle progressed `+3 pp` this cycle —
   it is still healthy.
