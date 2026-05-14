# Cycle 240 Results

## Worked on

§441 `Section441B.lean` closed-form witnesses for `cInverseLog n` at
`n = 2` and `n = 3`, plus stretch corollaries (negativity witnesses)
and Priority 3 cross-checks against cycle-238's general
`cInverseLog_neg` headline.

Per strategy Priority 0, the GPFS smoke test on
`OpenMath/Chapter4/Section441.lean` was **skipped** (44th consecutive
cycle).

## Approach

Verbatim port of cycle 237's `cInverseLog_one_eq_neg_one_sixth`
template — extract the `coeff (2n)` of `cInverseLogSeries * cSeries =
1` (the (441c) identity), expand `Finset.antidiagonal (2n)` literally
into an `insert ... singleton` chain, rewrite each
`coeff_cInverseLogSeries k` using `Even`/`¬ Even` simp facts, then
substitute the prior closed-form values for `coeff k cSeries`
(`k = 0, 2` for `n=2`; `k = 0, 2, 4` for `n=3`) and close with
`norm_num` + `linarith`.

Four theorems landed:

1. `cInverseLog_two_eq : cInverseLog 2 = -2 / 45` — Deliverable 1.A.
2. `cInverseLog_three_eq : cInverseLog 3 = -22 / 945` — Deliverable
   1.B, uses 1.A to substitute the `coeff 4 cSeries` term in the
   antidiagonal-6 expansion.
3. `cInverseLog_two_neg : cInverseLog 2 < 0` — Priority 2 stretch.
4. `cInverseLog_three_neg : cInverseLog 3 < 0` — Priority 2 stretch.

Priority 3 cross-checks (`example : cInverseLog 2 < 0 :=
cInverseLog_neg 2 _`, idem for `3`) added at end of file — both
elaborate, confirming cycle-238's strong-induction headline returns
the same sign as the closed-form values.

## Result

**SUCCESS.** All deliverables shipped axiom-clean.

* `lake env lean OpenMath/Chapter4/Section441B.lean` warm: ~5s, 0
  errors, 0 sorries.
* `lean_verify` on each new symbol returns
  `[propext, Classical.choice, Quot.sound]`:
  - `OpenMath.Chapter4.Section441B.cInverseLog_two_eq` ✓
  - `OpenMath.Chapter4.Section441B.cInverseLog_three_eq` ✓
  - `OpenMath.Chapter4.Section441B.cInverseLog_two_neg` ✓
  - `OpenMath.Chapter4.Section441B.cInverseLog_three_neg` ✓
* `Finset.antidiagonal 6 = {…}` via `by decide` worked without
  fallback (no need for `Finset.antidiagonal_succ` peeling — R1
  did not fire).
* `linarith` closed both residue equations after `norm_num`
  normalised the fractional coefficients — R3 did not fire.

No regression on cycle 237/238 lem:441B work; the
`cInverseLog_neg` strong-induction proof still elaborates and its
specialisations at 2, 3 type-check (Priority 3 cross-checks).

## Faithfulness check

### `cInverseLog_two_eq : cInverseLog 2 = -2 / 45`

* **Entity ID**: textbook-derivable from `lem:441B` recurrence; not
  separately catalogued. Butcher §441 p. 376 names only `c₀ = 1/2`
  and `c₂ = -1/6` explicitly, but the value `c₄ = -2/45` is a
  direct consequence of his (441c) recurrence.
* **Statement check**: Closed-form numerical value of `cInverseLog 2`,
  computed from (441c) at `coeff 4`. Captures the textbook content.
* **Tautology check**: PASS — conclusion is a specific rational
  value, not a hypothesis.
* **Identity check**: PASS — proof routes through
  `cInverseLogSeries_mul_cSeries_eq_one`, antidiagonal-4 expansion,
  five `coeff_cInverseLogSeries` evaluations, parity simp, and
  substitution of `cInverseLog_zero_eq_half` +
  `cInverseLog_one_eq_neg_one_sixth`. Real work.
* **Hypothesis strength check**: PASS — no hypotheses at all
  (closed numerical witness).

### `cInverseLog_three_eq : cInverseLog 3 = -22 / 945`

* **Entity ID**: same provenance — direct consequence of (441c).
* **Statement check**: Captures the textbook content.
* **Tautology check**: PASS.
* **Identity check**: PASS — proof uses antidiagonal-6 expansion
  (seven pairs), six `coeff_cInverseLogSeries` evaluations, parity
  simp, plus substitution of the three prior closed-form
  `cInverseLog 0, 1, 2` values. Genuinely does the work.
* **Hypothesis strength check**: PASS.

### `cInverseLog_two_neg`, `cInverseLog_three_neg`

* One-line `rw + norm_num` corollaries of the closed-form theorems.
* Tautology / identity check: PASS — they re-state the negativity
  as a sign claim, computing `-2/45 < 0` and `-22/945 < 0` via
  `norm_num`. Useful as non-vacuity witnesses for higher-order Phase
  C consumers.

### Cross-check `example` blocks

* Two `example` declarations — no name pollution. Just compile-time
  sanity checks that cycle-238's `cInverseLog_neg` general theorem
  applies at `n = 2, 3`. No new content, no faithfulness obligations.

### Global checks

* No definition smuggling, no `axiom`, no `maxHeartbeats` bump
  (file builds well under default).
* No `structure`/`class` introduced; no Prop-field hypothesis
  confusion to audit.
* All four new theorems pass axiom-cleanliness scan.

## Dead ends

None. Pre-flagged risks R1–R5 from the strategy did not fire:
* R1 (`by decide` slowness at antidiagonal 6): not observed — clean.
* R2 (`Even`/`¬ Even` for n=3, 5): handled cleanly via `by decide`.
* R3 (`linarith` numeric tractability for c₆): closed directly
  after `norm_num`.
* R4 (`unfold cInverseLog at this; simpa using this` idiom for
  h0/h2/h4): worked verbatim.
* R5 (`2 * 3 = 6` substitution): trivial `norm_num`.

## Discovery

* The cycle-237 antidiagonal-expansion template scales cleanly to
  antidiagonal-6 (and presumably higher even indices) without any
  modification to the structural skeleton: just more `insert` /
  `sum_insert` / `coeff_cInverseLogSeries k` / parity-simp lines,
  and one more `coeff k cSeries` substitution per prior `cInverseLog`
  value used. Marginal token cost per new `n`. Confirms the
  strategy's Cycle 241+ Option A is viable as bookkeeping work.
* `by decide` evaluates `Finset.antidiagonal 6 = {…}` at typecheck
  speed comparable to `antidiagonal 4`; no fallback needed.
* The Priority 3 cross-check `example` blocks elaborate
  instantaneously — confirms cycle-238's strong-induction `cInverseLog
  _neg` proof typechecks on its specialisations at `n = 2, 3` and is
  consistent with the closed-form witnesses. Provides a "general
  theorem ⟹ specific witness" sanity check that any future regression
  in cycle 238 would immediately surface.

## Suggested next approach

**Option B (§302 tree-combinatorics)** is the recommended next
direction per cycle-240 strategy outlook §241+. Highest single-cycle
ship rate, independent of GPFS and B-series, opens a fresh Chapter 3
textbook target. Candidates: `thm:302A`, `thm:302B`, `thm:302C`,
`thm:304A`.

**Option A (continue §441 closed forms at n=4, 5)** is viable but
marginal — the cycle-238 general headline already covers the
mathematical content for all `n ≥ 1`. Closed-form bookkeeping at
higher indices is mechanical token cost without new structure;
worth doing only if a downstream consumer specifically needs `c₈`
or `c₁₀` as concrete witnesses (none identified).

**Option C (§383 abstract-quotient `_composeQ_phi`)** remains
deferred; cycle 239 just shipped substantive §383 infrastructure
and should settle for at least one more cycle.

**Option D (§380s `thm:381G`, `thm:381H`)** still blocked on the
`Equivalent → PhiEquivalent` direction; multi-cycle B-series work.

GPFS-induced smoke test on `Section441.lean` continues to be
infeasible (44 consecutive timeouts); do NOT retry next cycle.
