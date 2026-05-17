# Cycle 348 Results

## Worked on

**Phase D′ Step 2 scoping for `def:422B`** — a scoping-only cycle
deferring all Lean code per the cycle 347 task results recommendation
(option A) and the cycle 200/201 rollback precedent forbidding multi-
cycle work without a phased plan.

Single deliverable: a new ≥200-line scoping document at
`.prover-state/issues/eq422a_eta_phase_D_prime_step_2_scoping.md`
(actual: 777 lines) laying out the multi-cycle plan for deriving
`0 ≤ coef_β(M)` from `IsStable + IsConsistent` alone — the
strengthening that would eliminate cycle 345's explicit `hβ_nn`
hypothesis from `Eq422a_at_vertex_eta_eq_of_stable_preconsistent`
(`Section422.lean:793`).

## Approach

Followed the cycle 348 strategy's eight-section template (mirroring
cycle 180 `lem_441A_phase_C_scoping.md`, cycle 260 `lem_310B_plan.md`,
and cycle 336 `def_422B_path.md` precedents):

1. **§1 — Textbook source**: re-read `extraction/raw_text/ch04.txt`
   regions §403 (stability, lines 145–164), §404 (consistency, lines
   166–236), §410 (order conditions, lines 619–700), §441 (Möbius
   transform + Lemma 441A/B + Thm 441C, lines 1933–2068), §451
   (G-stability, lines 2280–2463), and §452 (one-leg ↔ LMM, lines
   2465–2502). Quoted ≥5 textbook passages verbatim with line-number
   citations.

2. **§2 — Target theorem**: stated `coef_β_nonneg_of_stable_consistent`
   in both coefficient and polynomial forms (interchangeable via cycle
   347's bridge at `Section422.lean:957`).

3. **§3 — Infrastructure inventory**: verified 27 existing Lean symbols
   at HEAD `1b0fdef` via grep, organised by file (Section422, 410, 404,
   441, 451). Flagged `bdf2LMM_isConsistent` as `[MISSING]` (only
   `bdf2LMM_isPreconsistent` exists).

4. **§4 — Candidate routings**: documented **five** routes (A through
   E) with explicit LOC budget, cycle count, Mathlib-hook completeness,
   and dead-end risk for each.

5. **§5 — Phase decomposition**: 4 phases (D′.2.0 through D′.2.3) with
   per-phase LOC budgets totalling 140–270 LOC over 3–5 cycles.

6. **§6 — Risk assessment**: 6 risks (R1–R6) with mitigations.

7. **§7 — Cycle 349 entry point**: a concrete first-30/next-30/rest
   breakdown for the cycle 349 worker.

8. **§8 — Cross-references**: 14 cross-references to other scoping
   docs, Lean line numbers, and ch04.txt line numbers.

No Lean code was written this cycle. No sorries introduced.

## Result

**SUCCESS.** Scoping doc shipped at
`.prover-state/issues/eq422a_eta_phase_D_prime_step_2_scoping.md`.

Verification against the cycle 348 strategy §D checklist:

| Check | Status | Evidence |
|---|---|---|
| 1. File exists at HEAD | ✓ | created this cycle |
| 2. ≥200 lines | ✓ | 777 lines (well over) |
| 3. All 8 sections (§1–§8) | ✓ | each labelled `## §N` |
| 4. Each section substantive | ✓ | no empty placeholders |
| 5. §1 ≥3 lines quoted from ch04.txt | ✓ | 5 textbook quotes with line-number citations |
| 6. §3 ≥10 existing symbols verified | ✓ | 27 symbols across 5 files |
| 7. §4 ≥3 candidate routes | ✓ | 5 routes (A through E) with risk assessment |
| 8. §5 ≥3 phases with LOC budgets | ✓ | 4 phases (D′.2.0–D′.2.3) |
| 9. §7 cycle 349 entry point | ✓ | concrete first-30/next-30/rest breakdown |
| 10. git diff only new scoping file | ✓ | only `.prover-state/` changes |
| 11. zero new sorries | ✓ | `grep -c sorry OpenMath/Chapter4/Section422.lean` unchanged at 0 |

## Faithfulness check

**N/A** (no new Lean `def` / `structure` / `theorem` introduced this
cycle — scoping document only).

The scoping doc itself satisfies the cycle 348 strategy §E meta-
constraints:

* **No definition smuggling**: §4 explicitly flags Route D's order-2
  hypothesis-strengthening as a faithfulness risk; cycle 250's
  `alphaWeight` precedent cited in §6 R4.
* **Accurate textbook citation**: §1 quotes textbook passages with
  exact line-number citations (`ch04.txt:145–164`, `:166–236`,
  `:619–700`, `:1933–2068`, `:2280–2463`, `:2465–2502`).
* **Divergence risks flagged**: §6 lists 6 distinct risks (R1–R6) with
  per-risk mitigations.

## Dead ends

**Route A killed in scoping**: §4 Route A documents that the
straightforward α-side template port (mirroring cycles 175–178 with
`ρPoly` → `βPoly`) is **structurally inappropriate** because `βPoly`
has leading coefficient `M.β k`, which is not fixed by
`IsStable`/`IsConsistent` (explicit LMMs have `β k = 0`; BDF2 has
`β k = 0` too, making `βPoly` degree 0). The "go to +∞" argument that
underpins cycle 177's `ρPoly_pos_on_Ioi_one` has no β-side analog.
Cycle 349+ should not attempt Route A.

**Route B insufficient**: cycle 345's `coef_α_eq_sum_β_of_isConsistent`
gives `sum_β > 0` under stability + consistency (via cycle 344's
`coef_α > 0`). But `sum_β = Σᵢ βᵢ ≠ coef_β = Σᵢ i·βᵢ`. The (404b)
equation does not bridge the index-weighted form. Route B is therefore
useful as a **precursor** (`sum_β_pos_of_stable_consistent`) but does
NOT close Phase D′ Step 2.

**Route C deferred**: the §432 boundary-locus argument requires
complex-analytic infrastructure (Schur, Routh-Hurwitz) that parallels
`jordan_canonical_form_missing.md` and `rouche_theorem_missing.md`
Mathlib gaps. Route C is the fallback if Routes D and E both fail.

## Discovery

* **The textbook does NOT directly characterise `coef_β ≥ 0` under
  `IsStable + IsConsistent`.** Lemma 441A characterises the *Möbius-
  transformed* `aᵢ ≥ 0` (cycle 179 already shipped `a₁ > 0` partially),
  but there is no analogous Lemma 441B' for `bᵢ ≥ 0` or for
  `βPoly'(1) ≥ 0`. Theorem 441C only uses `b` as a remainder term.
  This is a substantive obstruction that was not visible from the
  cycle 347 task results alone — it requires the §441 re-reading to
  surface.

* **§452 one-leg perspective**: `coef_β / sum_β = coef_β / coef_α`
  (under consistency, by (404b)) is the **fractional time offset** for
  the underlying one-leg method (`x̄ₙ = xₙ − (coef_β / sum_β)·h`).
  This is the structural meaning of `coef_β`. The textbook does not
  state that this offset has a sign-definite value under stability +
  consistency.

* **§410 order-2 connection**: under order ≥ 2, `coef_β = (1/2)·
  Σᵢ i²·αᵢ` (from `C₂ = 0` coefficient matching). This is Route D's
  algebraic identity. It strengthens the hypothesis (order ≥ 2 vs.
  order ≥ 1) but provides a concrete algebraic route. **Whether
  `0 ≤ Σᵢ i²·αᵢ` is derivable from `IsStable + IsConsistent` alone
  (without the order-2 strengthening) is a substantive intermediate
  question** flagged in §5 Phase D′.2.1.

* **Route E (corollary reformulation) is a non-obvious win**:
  inspecting cycle 345's proof at `Section422.lean:804–806` reveals
  that the `hβ_nn : 0 ≤ coef_β(M)` hypothesis is consumed *only* via
  `linarith [hα_pos, hβ_nn]` to discharge the denominator non-
  vanishing condition `coef_α + coef_β ≠ 0`. The actual sufficient
  condition is weaker: `coef_α + coef_β = Σᵢ (i + 1)·βᵢ ≠ 0`. If
  this non-vanishing is derivable under `IsStable + IsConsistent`
  alone (with no sign claim), the corollary closes without ever
  proving `coef_β ≥ 0`. Discovered during §4 routing investigation.

* **`bdf2LMM_isConsistent` is missing**: only the preconsistency half
  (`bdf2LMM_isPreconsistent` at `Section441.lean:837`) exists at HEAD.
  The full (404b) half (≈10 LOC; `(4/3) + 2·(-1/3) = 2/3 = sum_β`)
  is a useful Phase D′.2.0 precursor and unblocks BDF2 sanity witnesses
  for the downstream Phase D′.2.x deliverables.

## Suggested next approach

**Cycle 349 default: enter Phase D′.2.0 per §5 of the new scoping
doc.**

Phase D′.2.0 ships:

1. `bdf2LMM_isConsistent` at `Section451.lean` (≈10 LOC, 1-line `And.
   intro`-style witness).
2. `sum_β_pos_of_stable_consistent` at `Section422.lean` (≈10 LOC,
   composes cycle 345's `coef_α_eq_sum_β_of_isConsistent` with cycle
   344's `coef_α_pos_of_stable_preconsistent`).
3. BDF2 numerical witness `bdf2LMM_sum_β_pos` (≈5 LOC).

Total: ≈30 LOC, single cycle. Establishes the precursor `sum_β > 0`
and unblocks downstream BDF2 witnesses.

**Cycle 349 textbook re-reading task**: per §7.1, spend the first 30
minutes confirming the §441 textbook obstruction (no Lemma 441B' on
β-side) and checking §432 boundary-locus for any sign-definite
constraint on `σ'(1)` under stability. If a constraint is found,
amend this scoping doc rather than implementing Phase D′.2.1.

**Cycle 350+ (Phase D′.2.1)**: Routes E (corollary reformulation) and
D (order-2 strengthening) are co-equal in difficulty (~100–150 LOC).
Cycle 349's textbook re-reading should decide between them. Route E
is preferred because it avoids hypothesis-strengthening and produces
a clean unconditional `Eq422a_at_vertex_eta_eq_of_stable_consistent`
corollary in 1–2 cycles.

**Alternative pivot (if R5 streak burnout warranted)**: per cycle 347
task results option C, the planner may legitimately pivot to a fresh
entity (`def:451A` G-stability, `thm:535A` GLM underlying one-step,
or `thm:541A` DIMSIM types) rather than continuing the §422 streak
beyond cycle 16. The cycle 348 scoping doc is structured so that
cycle 349+ can resume Phase D′ Step 2 at any future date without
re-scoping.
