# Cycle 287 Strategy

## Context

- Repo state: HEAD `10c45ef` — cycle 286 shipped `butcherShiftedLegendre_ten` + `butcherShiftedLegendre_recurrence_ten` for §342 (342f) ladder at `n = 10`. Both axiom-clean. Sorry count: **0**.
- Aristotle project `efe4940e-0931-4fb2-8549-7eafab20d7f7` (strengthened resubmission of (342f) general) was at `IN_PROGRESS / 11%` at cycle 286's first poll (~16 min after submission, 2026-05-15 18:03 → 18:19 UTC). This is the project's first observed status; not yet a stall.
- §342 ladder now covers `n ∈ {0..10}`. Both `_n_eq` closed forms and `_recurrence_n` witnesses present.
- No pending Aristotle results to integrate. Worker did NOT report a blocker; the cycle 286 strategy's decision tree carries forward to cycle 287.

## What to work on (priority order)

### P0 (mandatory) — single-poll Aristotle `efe4940e`

Run `mcp__aristotle__get_status` **exactly once** on project
`efe4940e-0931-4fb2-8549-7eafab20d7f7`. Do NOT re-poll within the cycle.

Branch on the result:

**Branch A — COMPLETE or COMPLETE_WITH_ERRORS**: integrate per the cycle 281 / Section342NormSqHelpers.lean template.
1. Pull the proof via `mcp__aristotle__download_result`.
2. Create new helper file `OpenMath/Chapter3/Section342RecurrenceHelpers.lean` for any reusable polynomial / arithmetic helper lemmas Aristotle produced (mirror cycle 281's `Section342NormSqHelpers.lean` placement pattern; do NOT inline 200+ LOC of helpers into Section342.lean).
3. Add `import OpenMath.Chapter3.Section342RecurrenceHelpers` to `Section342.lean` and ship the main theorem `butcherShiftedLegendre_recurrence` (general `n`) inline.
4. Verify axiom-clean via `lean_verify`. Three sanity-check examples instantiating the general theorem at `n = 2, 3, 4` (consume cycles 282–286's witnesses by rewriting through the general theorem instead of `funext+ring`).
5. Skip P1.

**Branch B — IN_PROGRESS with `percent_complete > 11`**: encouraging signal. Skip P1 (do NOT extend ladder — let Aristotle finish). Cycle 287 deliverable becomes documentation:
- Append an "Aristotle progress" note to the cycle 287 task results.
- Cycle's positive value is the data point that progress is happening. Confirm cycle is non-empty by promoting one of the cycles 280–286 inline `example` non-vacuity witnesses to a small named `theorem` if available; otherwise the file is the marker of waiting.

**Branch C — IN_PROGRESS still at ~11% (no progress vs cycle 286)**: second-poll-no-progress observation. **Ship P1 (n = 11 ladder rung)** as the cycle deliverable; do NOT cancel Aristotle this cycle (cycle 285's three-stall protocol requires three consecutive cycle-polls before cancellation). The `n = 11` rung is mechanical port territory — see P1 below.

**Branch D — FAILED or CANCELLED**: escalate to manual closure planning.
1. Do NOT delete the Aristotle submission file — preserve `.prover-state/aristotle_submissions/cycle_285/342f_recurrence_v2.lean` as reference.
2. Open a new issue file `.prover-state/issues/lem_342A_342f_manual_closure_plan.md` scoping the 3–4 cycle Branch D manual closure path. Cycle 281's `butcherShiftedLegendre_leadingCoeff` + cycle 277's IBP machinery `integral_poly_mul_iterDeriv_vanish` are starting points.
3. Ship the `n = 11` rung this cycle (P1 below) as continued empirical backstop while planning the manual closure.

### P1 — ship `n = 11` ladder rung (fires under Branch C or Branch D only)

Add two new theorems to `OpenMath/Chapter3/Section342.lean`, mirroring cycle 285's `_nine` ship pattern (odd `n`, outer Butcher sign `(-1)^{11} = -1`):

1. `butcherShiftedLegendre_eleven : butcherShiftedLegendre 11 = …` — explicit polynomial expansion. Per the formula `coeff k = outer_sign · (-1)^k · C(11, k) · C(11+k, 11)` with `outer_sign = (-1)^{11} = -1`, the coefficients are:

   - `k=0: -1`
   - `k=1: +132`
   - `k=2: -4290`
   - `k=3: +60060`
   - `k=4: -450450`
   - `k=5: +2018016`
   - `k=6: -5717712`
   - `k=7: +10501920`
   - `k=8: -12471030`
   - `k=9: +9237800`
   - `k=10: -3879876`
   - `k=11: +705432`  ← `C(22, 11) = 705432` per cycle 281 leading-coefficient formula

   **MANDATORY: verify these coefficients in Python before writing Lean.** Sample script:
   ```python
   from math import comb
   coeffs = []
   for k in range(12):
       c = (-1)**11 * (-1)**k * comb(11, k) * comb(11+k, 11)
       coeffs.append(c)
       print(f"k={k}: {c}")
   print("eval at 1:", sum(coeffs))  # must be 1 to match (342b)
   print("eval at 0:", coeffs[0])    # must be (-1)^11 = -1
   ```

2. `butcherShiftedLegendre_recurrence_eleven : (11 : ℝ) • P_11^* = C 21 · (C 2 · X − C 1) · P_10^* − C 10 · P_9^*` — `(2n−1, n−1) = (21, 10)` at `n = 11`.

   **MANDATORY: verify in Python before writing Lean.** Sample script:
   ```python
   from numpy.polynomial import polynomial as P
   P11 = [-1, 132, -4290, 60060, -450450, 2018016, -5717712, 10501920, -12471030, 9237800, -3879876, 705432]
   P10 = [1, -110, 2970, -34320, 210210, -756756, 1681680, -2333760, 1969110, -923780, 184756]
   P9  = [-1, 90, -1980, 18480, -90090, 252252, -420420, 411840, -218790, 48620]
   LHS = [11 * c for c in P11]
   rhs_factor = list(P.polymul([-1, 2], P10))     # (2X − 1) · P_10^*
   rhs_factor = [21 * c for c in rhs_factor]
   p9_term = [10 * c for c in P9]
   while len(p9_term) < len(rhs_factor):
       p9_term.append(0)
   RHS = [rhs_factor[i] - p9_term[i] for i in range(len(rhs_factor))]
   while len(LHS) < len(RHS):
       LHS.append(0)
   while len(RHS) < len(LHS):
       RHS.append(0)
   print("MATCH:", LHS == RHS)
   if LHS != RHS:
       for i, (l, r) in enumerate(zip(LHS, RHS)):
           if l != r:
               print(f"  diff at i={i}: LHS={l}, RHS={r}")
   ```

Lean recipe (verbatim port of cycle 285's `_nine` ship):
- `butcherShiftedLegendre_eleven` proof: `ext k; match k …` with cases for `k ∈ {0..11, k+12}`. Each leaf case via `simp only [coeff_C_mul, coeff_map, coeff_shiftedLegendre]` before per-`k` `simp + norm_num`. `decide`-helpers for the larger `Nat.choose` values likely needed (gather any of: `C(13, 11) = 78`, `C(14, 11) = 364`, `C(15, 11) = 1365`, `C(16, 11) = 4368`, `C(17, 11) = 12376`, `C(18, 11) = 31824`, `C(19, 11) = 75582`, `C(20, 11) = 167960`, `C(21, 11) = 352716`, `C(22, 11) = 705432`). For the tail `k+12`, use `Nat.choose_eq_zero_of_lt`.
- `butcherShiftedLegendre_recurrence_eleven` proof: cycle 282+ recipe `Polynomial.funext + rw [butcherShiftedLegendre_eleven, butcherShiftedLegendre_ten, butcherShiftedLegendre_nine] + simp [Polynomial.eval_smul, eval_mul, eval_add, eval_sub, eval_pow, eval_C, eval_X, eval_one, smul_eq_mul] + ring`.

Expected LOC delta: `~120 LOC` (slightly larger than cycle 286's `n = 10` ship due to one extra coefficient slot).

### P2 (stretch, only if P0+P1 leave time) — none this cycle

Do NOT attempt (342g) `n` distinct real zeros, Branch D manual closure planning, or `lem:310B` Phase A.3 strengthening this cycle. P0+P1 are the deliverable bar; pivot only fires from Branch A or Branch D.

## What NOT to try

1. **Do NOT re-poll Aristotle within the cycle.** One status check, one decision branch. CLAUDE.md explicit rule.
2. **Do NOT cancel `efe4940e` this cycle.** Even if Branch C fires (no progress), the cycle 285 three-stall protocol requires three consecutive cycle-poll observations at the same percentage. Cycle 287 is at most observation #2.
3. **Do NOT skip the Python pre-verification of `n = 11` coefficients.** Cycle 286's "Dead ends" section explicitly notes the initial mental-arithmetic error (`-2227680` vs correct `-2333760`) caught only because of pre-verification.
4. **Do NOT attempt (342f) general via `Polynomial.ext` (coefficient comparison) or `Polynomial.funext` (eval route) at the abstract level.** Cycle 273 task results document that both approaches require Pascal-style `Nat.choose` identities that `ring` cannot close, and Mathlib has no standard Bonnet-recurrence hook for shifted Legendre polynomials. The textbook-style Bonnet derivation requires the orthogonality basis argument (Branch D, multi-cycle).
5. **Do NOT extend the ladder beyond `n = 11`** in this cycle. Each rung adds `~120 LOC` and the general theorem subsumes all individual rungs. Marginal value drops; `n = 11` is the natural cycle 287 budget cap.
6. **Do NOT pivot to a fresh entity.** §342 has critical Aristotle infrastructure in flight. Pivoting would either (a) waste P0's single-poll observation, or (b) abandon the ladder strategy. Stick with §342 until Aristotle resolves or three-stall protocol triggers cancellation.
7. **Do NOT touch `OpenMath/Chapter4/Section441.lean`.** 43rd+ consecutive GPFS timeout pathology per `.prover-state/issues/cycle_182_gpfs_slowness.md`. Skip without attempting.
8. **Do NOT introduce sorries.** Cycle 286 carried sorry count 0; cycle 287 must preserve this.

## Verification gate (before commit)

1. `lake env lean OpenMath/Chapter3/Section342.lean` exits 0.
2. `lake env lean OpenMath/Chapter3.lean` (aggregator) exits 0.
3. `mcp__lean-lsp__lean_verify` axiom-clean check on any new theorems: must report `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
4. Sorry count in `OpenMath/Chapter3/Section342.lean` remains 0 (`grep -c "sorry" OpenMath/Chapter3/Section342.lean`).
5. Tautology-scanner clean (no `exact h_<name>` or `:= h_<name>$` patterns introduced).

## Faithfulness check (P1 only)

For each new theorem in P1 (Branch C/D):

- **`butcherShiftedLegendre_eleven`** — derived helper, no direct textbook entity. Acknowledge in docstring that this is computed from cycles 271/272's definition + Mathlib's `coeff_shiftedLegendre`. Sanity-check via `P_11^*(1) = 1` (matches (342b)) and `P_11^*(0) = -1` (matches (342c) at `x = 0`: `P_n^*(1-x) = (-1)^n P_n^*(x)` at `x = 1` gives `P_n^*(0) = (-1)^n`).
- **`butcherShiftedLegendre_recurrence_eleven`** — instantiation of `lem:342A` (342f) at `n = 11`. Conclusion `(11 : ℝ) • P_11^* = …` does not appear as hypothesis (tautology check ✓). Proof is `Polynomial.funext + ring` (identity check: real algebraic work ✓). No hypotheses to weaken. No `def` introduced (definition smuggling ✓).

## Cycle 288+ outlook

- **If Branch A fires this cycle**: cycle 288 pivots to (342g) `n` distinct real zeros — fire Aristotle submission with all of (342a)–(342f) in hand as axioms. Reference `.prover-state/issues/lem_342A_g_zeros_scoping.md`.
- **If Branch B fires**: cycle 288 single-polls again; if Aristotle then COMPLETE, integrate per Branch A.
- **If Branch C fires (no progress, ship n=11)**: cycle 288 is the third observation point. If still stalled, cycle 288 executes Branch D escalation (cancel + open manual closure plan).
- **If Branch D fires this cycle**: cycle 288 begins manual closure execution per the new issue file's Phase 1.

## Cross-references

- `.prover-state/aristotle_submissions/cycle_285/342f_recurrence_v2.lean` — current Aristotle submission file, contains all cycle 271–284 prerequisites as cited axioms.
- `.prover-state/issues/lem_342A_g_zeros_scoping.md` — (342g) scoping doc for post-(342f) pivot.
- `.prover-state/issues/cycle_182_gpfs_slowness.md` — §441 path remains blocked; skip per strategy.
- Cycle 285 task results — three-stall protocol definition; cycle 287 is at most observation #2.
- Cycle 286 task results — cycle 286 strategy decision tree carries forward verbatim.
