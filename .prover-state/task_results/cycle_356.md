# Cycle 356 Results

## Worked on
Per the planner's §A–§C strategy: ship three mandatory (P1–P3) +
three stretch (P4a–P4c) **numerical non-vacuity witnesses** in
`OpenMath/Chapter4/Section422.lean` extending the cycle 355 consumer
matrix from {BDF2, BDF3, trapezoidal} to the full five-LMM coverage
matrix {explicit Euler, implicit Euler, trapezoidal, BDF2, BDF3} at
cycle 349's `sum_β_pos_of_stable_consistent` and cycle 350's
`Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened` ships.

* **P1 — implicit Euler D′.2.0 `sum_β_pos` example** (anonymous
  `example`, ~7 LOC). Direct invocation of cycle 349's
  `sum_β_pos_of_stable_consistent` with `implicitEulerLMM_isStable`
  + `implicitEulerLMM_isConsistent`. Concludes `0 < 1 + 0 = 1` at
  the implicit Euler LMM.
* **P2 — `implicitEulerLMM_coef_α_plus_coef_β_ne_zero`** (named
  `theorem`, ~7 LOC). Numerical witness for the cycle 350
  weakened-hypothesis ship at implicit Euler: `coef_α + coef_β =
  1 + 0 = 1 ≠ 0`.
* **P3 — end-to-end implicit Euler `η(τ) = 1` example** (anonymous
  `example`, ~14 LOC). Direct exercise of
  `Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened` on
  implicit Euler, discharging the weakened non-vanishing hypothesis
  via P2. Conclusion `η(τ) = sum_β / (coef_α + coef_β) = 1 / 1 = 1`.
* **P4a — explicit Euler D′.2.0 `sum_β_pos` example** (anonymous
  `example`, ~7 LOC). Direct invocation of
  `sum_β_pos_of_stable_consistent` with `explicitEulerLMM_isStable`
  + `explicitEulerLMM_isConsistent`. Concludes `0 < 0 + 1 = 1` at
  the explicit Euler LMM.
* **P4b — `explicitEulerLMM_coef_α_plus_coef_β_ne_zero`** (named
  `theorem`, ~8 LOC). Numerical witness for the cycle 350
  weakened-hypothesis ship at explicit Euler: `coef_α + coef_β =
  1 + 1 = 2 ≠ 0`.
* **P4c — end-to-end explicit Euler `η(τ) = 1/2` example** (anonymous
  `example`, ~14 LOC). Direct exercise of
  `Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened` on
  explicit Euler, discharging the weakened non-vanishing hypothesis
  via P4b. Conclusion `η(τ) = sum_β / (coef_α + coef_β) =
  1 / 2 = 1/2` — distinct from the BDF2 / implicit Euler `η(τ) = 1`
  and trapezoidal `η(τ) = 2/3` numerical pinnings.

Six additions total. No new entities. No `class`/`structure`
changes. No sorries opened. No `axiom`/`constant` introduced.

## Approach
Each priority is a mechanical composition of existing axiom-clean
infrastructure:
* P1, P4a: one-liner term-mode application of
  `sum_β_pos_of_stable_consistent`. Three arguments (`hk`,
  `hStable`, `hConsistent`) discharged via `by norm_num` and the
  named LMM-specific witnesses from `Section404`.
* P2, P4b: `simp [<LMM>, …]` — see "Discovery" below for the
  surprising linter-driven simplification (no `norm_num` needed at
  `k = 1` for these specific LMMs).
* P3, P4c: `have h := <weakened ship> ...; rw [h]; simp + (norm_num
  when needed)`. Numerical β-sum identities `1/1 = 1` (implicit
  Euler) and `1/2 = 1/2` (explicit Euler).

Verification ran `lake env lean OpenMath/Chapter4/Section422.lean`
on the full file; the build succeeded cleanly. Sorry-count remains 0.

## Result
SUCCESS — all six priorities shipped (3 mandatory + 3 stretch).
File grew from 1487 → 1576 LOC (~89 LOC added, slightly more than
the planner's ~70 LOC estimate due to interleaving the implicit
Euler and explicit Euler blocks in three logically-grouped P/P4
pairs at three insertion points). No upstream regressions; the
§404 explicit-Euler and implicit-Euler witnesses (consistency,
stability, preconsistency from cycles 250-262 in Section404) all
wire correctly into §422's `sum_β_pos_of_stable_consistent` /
`Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened`
infrastructure.

## Faithfulness check
**Cycle 356 introduces no new `def` and no new `class`/`structure`.**
Two new named `theorem`s (P2, P4b); four anonymous `example`s
(P1, P3, P4a, P4c). Anonymous examples are non-vacuity discharges,
not theorem claims; no entity ID to cite.

### P2 — `implicitEulerLMM_coef_α_plus_coef_β_ne_zero`
* No textbook entity ID; this is a *consumer-witness* lemma (not a
  Butcher-named statement), parallel to cycle 350's
  `bdf2LMM_coef_α_plus_coef_β_ne_zero` and cycle 355's
  `trapezoidalLMM_coef_α_plus_coef_β_ne_zero`.
* The Lean statement instantiates the named-LMM-independent
  denominator `(∑ i : Fin k, (i+1)·α i.succ) + (∑ i : Fin (k+1),
  i·β i)` at `k = 1` with `M = implicitEulerLMM`. The numerical
  fact `1 ≠ 0` follows by `simp` on the explicit `α = (-1, 1)`,
  `β = (1, 0)` coefficient vectors.
* Definition smuggling: N/A (no new `def`).
* Tautology / identity / hypothesis-strength: N/A (no hypotheses).

### P4b — `explicitEulerLMM_coef_α_plus_coef_β_ne_zero`
* Same shape as P2, at `k = 1` with `M = explicitEulerLMM`.
  Numerical fact `2 ≠ 0` per `explicitEulerLMM.α = (-1, 1)`,
  `explicitEulerLMM.β = (0, 1)`.
* Faithfulness checks: all N/A (no hypotheses; no new `def`).

### Pre-commit faithfulness checklist
* Tautology check: P2, P4b conclusions (`... ≠ 0`) are not among
  their (empty) hypothesis lists. ✓
* Identity check: P2, P4b proofs are `simp ...`, doing real
  arithmetic work (β-coefficient unfolding + `if`-discriminant
  reduction); not `exact h` re-exports. ✓
* Definition smuggling: no new `def`. ✓
* Hypothesis strength: P2, P4b have no hypotheses; cannot be too
  strong. P1, P3, P4a, P4c examples invoke existing infrastructure
  with the exact hypothesis-signatures of
  `sum_β_pos_of_stable_consistent` /
  `Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened` —
  no strengthening. ✓
* Absent theorem check: no promised `sorry`s. The file's sorry count
  remains 0. ✓

## Dead ends
None. One mid-cycle linter adjustment: the initial drafts of P2 and
P3 mirrored cycle 355's trapezoidal recipe (`simp [<LMM>,
Fin.sum_univ_two]; norm_num`), but the `unusedSimpArgs` /
`No goals to be solved` linters flagged that `simp [implicitEulerLMM]`
alone closes both P2 and P3 — the β = (1, 0) coefficient nullifies
the i=1 term of the Fin 2 β-sum, so `simp`'s if-discriminant
reduction collapses the entire denominator to `1` without
`Fin.sum_univ_two` cascading. P4b retained `Fin.sum_univ_two`
(β = (0, 1) needs unfolding the i=1 term) but `norm_num` was
unnecessary (simp closes `2 ≠ 0` via OfNat normalization).

## Discovery
**LMM-dependent simp-closure asymmetry at `k = 1`**: the canonical
cycle 355 recipe `simp [<LMM>, Fin.sum_univ_two]; norm_num` for
the coef_α+coef_β ne-zero witness *over-provisions* for two of
the four `k = 1` LMMs we've now covered:
* `implicitEulerLMM` (β = (1, 0)): `simp [implicitEulerLMM]`
  closes the goal. Both `Fin.sum_univ_two` AND `norm_num` are
  redundant. (The β 1 = 0 nullification collapses the denominator
  before Fin.sum_univ_two needs to fire.)
* `explicitEulerLMM` (β = (0, 1)): `simp [explicitEulerLMM,
  Fin.sum_univ_two]` closes the goal. `norm_num` is redundant.
  (Simp normalizes `2 ≠ 0` via the OfNat / `Ne` rewrite system.)
* `trapezoidalLMM` (β = (1/2, 1/2)): `simp [trapezoidalLMM,
  Fin.sum_univ_two]; norm_num` is the full recipe. (β has no
  vanishing entries, so the denominator computes to `3/2` and
  `norm_num` closes the rational ne-zero.)

The cycle 355 recipe is the *upper bound* — strip simp args and
norm_num until the linter is silent. The base cases are:
1. β has a vanishing entry that nullifies the i=1 β-term —
   `simp [<LMM>]` alone suffices (P2 implicit Euler).
2. β has no vanishing entries and the denominator is rational —
   full recipe needed (P3 trapezoidal cycle 355).
3. β has no vanishing entries but the denominator is integer —
   `simp [<LMM>, Fin.sum_univ_two]` suffices (P4b explicit Euler).

This pattern generalizes: for future `k = 1` LMM witnesses, draft
with the full recipe, then drop linter-flagged args. Do not
over-engineer the initial draft.

**Five-LMM coverage matrix milestone**: cycles 349 → 350 → 355 → 356
have now produced the complete `{explicitEulerLMM, implicitEulerLMM,
trapezoidalLMM, bdf2LMM, bdf3LMM} × {sum_β_pos_of_stable_consistent,
Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened}` consumer
witness matrix. All five canonical LMMs in the codebase exercise
both Phase D′.2.0 and Phase D′.2.1 ships at their natural numerical
conclusions:
* `sum_β` values: 1 (explicit/implicit Euler), 1 (trapezoidal),
  2/3 (BDF2), 6/11 (BDF3).
* `η(τ)` values: 1/2 (explicit Euler), 1 (implicit Euler, BDF2),
  2/3 (trapezoidal). BDF3 is in the matrix at the `sum_β_pos`
  level only; an end-to-end η witness for BDF3 (`η(τ) = 6/11`?)
  is the natural one-more-cycle stretch, but the planner did not
  include it in cycle 356's scope.

**Axiom-clean confirmation**: `#print axioms` for both P2 and P4b
returns exactly `[propext, Classical.choice, Quot.sound]` — the
standard logic axioms only, no `sorryAx` or non-standard axioms.

## Suggested next approach
The cycle 355 task results listed three priorities for next-cycle.
Cycle 356 picked option 1 (continue Phase D′ consumer wins) and
extended it to the maximum-density five-LMM coverage. Updated
priorities for cycle 357:

* **End-to-end BDF3 η witness (low-priority finish)**: ~15 LOC
  one-liner mirroring P4c with `bdf3LMM_coef_α_plus_coef_β_ne_zero`
  (already shipped cycle 355). Would extend the η(τ) consumer
  matrix to all five LMMs. Single-cycle work but the cycle 357
  planner should weigh marginal value against pivoting.
* **Pivot to Phase D.3 scoping (HIGH-VALUE multi-cycle prep)**: the
  inductive step of `underlyingOneStepMethod_aux`'s well-founded
  recursion (per `.prover-state/issues/def_422B_path.md` §5)
  remains the principal multi-cycle gap in `def:422B`. A dedicated
  scoping cycle to draft the linear-equation solver phase
  decomposition for `r(t) ≥ 2` trees would unblock §422's eventual
  `def:422B` Phase E sealing. Recommended as the next non-trivial
  forward-progress step.
* **Pivot to fresh entity (cycles 336–356 are 21 consecutive §422
  cycles)**: candidates per `cycle_336_pivot_options.md`:
  `def:451A` (G-stability witnesses), `thm:535A` (one-step
  underlying method for GLMs), `thm:541A` (DIMSIM types). All
  low-risk single-cycle ships. A fresh-entity diversification may
  reduce streak-burnout risk.
* **Phase D′.2.2 Step 2 scoping continuation** (the unconditional
  `0 ≤ coef_β` derivation from `IsStable + IsConsistent` alone) is
  still a multi-cycle target — Routes A/B/C/D blocked per the cycle
  348 scoping doc; the cycle 351 worker shipped Route D Step 1 but
  Step 2 needs `0 ≤ Σᵢ i²·αᵢ` infrastructure that isn't in the
  codebase yet.
