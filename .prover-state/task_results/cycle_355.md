# Cycle 355 Results

## Worked on
Per the planner's §A–§C strategy: ship four mandatory + one stretch
**numerical non-vacuity witnesses** in `OpenMath/Chapter4/Section422.lean`
that exercise the cycle 354 stability ships (`trapezoidalLMM_isStable`,
`bdf3LMM_isStable`) at downstream §422 consumers.

* **P1 — trapezoidal D′.2.0 `sum_β_pos` example** (anonymous `example`,
  ~7 LOC). Direct invocation of cycle 349's
  `sum_β_pos_of_stable_consistent` with cycle 354's
  `trapezoidalLMM_isStable` + cycle 352's `trapezoidalLMM_isConsistent`.
  Concludes `0 < 1/2 + 1/2 = 1` at the trapezoidal LMM.
* **P2 — BDF3 D′.2.0 `sum_β_pos` example** (anonymous `example`,
  ~7 LOC). Same shape with cycle 354's `bdf3LMM_isStable` + cycle 353's
  `bdf3LMM_isConsistent`. Concludes `0 < 6/11 + 0 + 0 + 0 = 6/11` at
  BDF3.
* **P3 — `trapezoidalLMM_coef_α_plus_coef_β_ne_zero`** (named `theorem`,
  ~10 LOC). Numerical witness for the cycle 350 weakened-hypothesis
  ship at trapezoidal: `coef_α + coef_β = 1 + 1/2 = 3/2 ≠ 0`.
* **P4 — `bdf3LMM_coef_α_plus_coef_β_ne_zero`** (named `theorem`,
  ~10 LOC). Same shape at BDF3: `coef_α + coef_β = 6/11 + 0 = 6/11
  ≠ 0`.
* **P5 (stretch) — end-to-end trapezoidal `η(τ) = 2/3` example**
  (anonymous `example`, ~15 LOC). Direct exercise of
  `Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened` on
  trapezoidal, discharging the weakened non-vanishing hypothesis via
  P3. Conclusion `η(τ) = sum_β / (coef_α + coef_β) = 1/(3/2) = 2/3`.

Five additions total. No new entities. No `class`/`structure` changes.
No sorries opened. No `axiom`/`constant` introduced.

## Approach
Each priority is a mechanical composition of existing axiom-clean
infrastructure:
* P1, P2: one-liner term-mode application of
  `sum_β_pos_of_stable_consistent`. The three arguments (`hk`,
  `hStable`, `hConsistent`) are discharged via `by norm_num` (the
  `0 < k` side-condition) and the named LMM-specific witnesses.
* P3, P4: `simp [<LMM>, Fin.sum_univ_<n>] ; norm_num`. Mirror of
  cycle 350's `bdf2LMM_coef_α_plus_coef_β_ne_zero` recipe at the
  trapezoidal (`k = 1`) and BDF3 (`k = 3`) instantiations.
* P5: `have h := <weakened ship> ...; rw [h]; simp + norm_num` on the
  numerical β-sum identity `(1/2 + 1/2) / (1 · 1 + 0 · (1/2) +
  1 · (1/2)) = 1 / (3/2) = 2/3`.

Verification ran `lake env lean OpenMath/Chapter4/Section422.lean`
on the full file; the build succeeded cleanly. Sorry-count remains 0.

## Result
SUCCESS — all five priorities shipped. File grew from 1419 → ~1469
LOC. No upstream regressions; the §404 trapezoidal and §451 BDF3
witnesses (consistency, stability, preconsistency) all wire correctly
into §422's `sum_β_pos_of_stable_consistent` /
`Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened` /
underlying-`(i+1)`-weighted-β denominator infrastructure.

## Faithfulness check
**Cycle 355 introduces no new `def` and no new `class`/`structure`.**
Two new named `theorem`s (P3, P4); three anonymous `example`s (P1, P2,
P5). Anonymous examples are non-vacuity discharges, not theorem claims;
no entity ID to cite.

### P3 — `trapezoidalLMM_coef_α_plus_coef_β_ne_zero`
* No textbook entity ID; this is a *consumer-witness* lemma (not a
  Butcher-named statement), parallel to cycle 350's
  `bdf2LMM_coef_α_plus_coef_β_ne_zero`.
* The Lean statement instantiates the named-LMM-independent
  denominator `(∑ i : Fin k, (i+1)·α i.succ) + (∑ i : Fin (k+1),
  i·β i)` at `k = 1` with `M = trapezoidalLMM`. The numerical fact
  `3/2 ≠ 0` follows by `simp + norm_num` on the explicit `α =
  (-1, 1)`, `β = (1/2, 1/2)` coefficient vectors.
* Definition smuggling: N/A (no new `def`).
* Tautology / identity / hypothesis-strength: N/A (no hypotheses).

### P4 — `bdf3LMM_coef_α_plus_coef_β_ne_zero`
* Same shape as P3, at `k = 3` with `M = bdf3LMM`. Numerical fact
  `6/11 ≠ 0` per `bdf3LMM.α = (-1, 18/11, -9/11, 2/11)`,
  `bdf3LMM.β = (6/11, 0, 0, 0)`.
* Faithfulness checks: all N/A (no hypotheses; no new `def`).

### Pre-commit faithfulness checklist
* Tautology check: P3, P4 conclusions (`... ≠ 0`) are not among
  their (empty) hypothesis lists. ✓
* Identity check: P3, P4 proofs are `simp ... ; norm_num`, doing real
  arithmetic work; not `exact h` re-exports. ✓
* Definition smuggling: no new `def`. ✓
* Hypothesis strength: P3, P4 have no hypotheses; cannot be too
  strong. P1, P2, P5 examples invoke existing infrastructure with
  the exact hypothesis-signatures of `sum_β_pos_of_stable_consistent`
  / `Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened` —
  no strengthening. ✓
* Absent theorem check: no promised `sorry`s. The file's sorry count
  remains 0. ✓

## Dead ends
None. The strategy explicitly anticipated `Fin.sum_univ_four` as the
only risk point (BDF3 β-side); it fired on first try via
`Fin.sum_univ_three` + `Fin.sum_univ_four` (both are stock Mathlib
lemmas), so no fallback was needed.

## Discovery
The `Fin.sum_univ_<n>` family covers `n = 0..8` in
`Mathlib.Algebra.BigOperators.Fin`. `simp [<LMM>, Fin.sum_univ_<n>,
Fin.sum_univ_<m>]; norm_num` is the canonical recipe for closing
numerical witnesses of the form "explicit-coefficient LMM satisfies
linear/rational arithmetic identity". Two `Fin.sum_univ_<n>` lemmas
suffice when both the α (`Fin k`) and β (`Fin (k+1)`) sides need
unfolding.

Trapezoidal's `α := fun i => if i = 0 then -1 else 1` formulation
(rather than `match`) does **not** require a special pattern — `simp`
handles the `if`-discriminant reduction at `i.succ : Fin 1` (which
reduces to `Fin.mk 1 _`, hence `i ≠ 0`) cleanly.

**Linter tightening note**: the initial draft of P3 and P5 passed
`Fin.sum_univ_one` as a simp argument for the `Fin 1` α-side, but
the Mathlib `unusedSimpArgs` linter flagged it: at `k = 1`,
`simp` reduces the α-side via the `Fin.sum_univ_two`-anchored
β-side closure (or via direct `Fin.sum_univ_succ` cascading) and
does not need `Fin.sum_univ_one` explicitly. Dropping the redundant
hint silences the linter without changing the proof's behaviour.
Future P3-style witnesses at `k = 1` can omit `Fin.sum_univ_one`
preemptively.

**Axiom-clean confirmation**: `#print axioms` for both P3 and P4
returns exactly `[propext, Classical.choice, Quot.sound]` — the
standard logic axioms only, no `sorryAx` or non-standard axioms.

## Suggested next approach
* **Continue Phase D′ consumer wins** at the remaining §404 LMM
  witnesses: implicit Euler (`implicitEulerLMM_sum_β_pos`,
  `implicitEulerLMM_coef_α_plus_coef_β_ne_zero`, end-to-end η witness).
  This would complete the five-LMM coverage matrix (explicit Euler +
  implicit Euler + trapezoidal + BDF2 + BDF3) for the cycle 349/350
  ships, in another ~30–40 LOC pure-additions cycle.
* **Pivot to Phase D.3 scoping**: the inductive step of
  `underlyingOneStepMethod_aux`'s well-founded recursion (per
  `.prover-state/issues/def_422B_path.md` §5) remains the principal
  multi-cycle gap in `def:422B`. A dedicated scoping cycle to draft
  the linear-equation solver phase decomposition for `r(t) ≥ 2` trees
  would unblock §422's eventual `def:422B` Phase E sealing.
* **Phase D′.2.2 Step 2 scoping continuation** (the unconditional
  `0 ≤ coef_β` derivation from `IsStable + IsConsistent` alone) is
  also a multi-cycle target — Routes A/B/C/D blocked per the cycle
  348 scoping doc; the cycle 351 worker shipped Route D Step 1 but
  Step 2 needs `0 ≤ Σᵢ i²·αᵢ` infrastructure that isn't in the
  codebase yet.
