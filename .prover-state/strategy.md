# Cycle 348 strategy — Phase D′ Step 2 scoping for `def:422B`

## A. Summary

Cycle 347 shipped Phase D′ Step 1 (the `coef_β ↔ βPoly'(1)` bridge)
axiom-clean. The `def:422B` chain has now absorbed **12 consecutive
cycles** (336–347): wire-up sanity → D-operator → Group.zpow API →
Eq422a predicate → τ-additivity infrastructure → closed-form η(τ)
solver → WellFoundedRelation → α-side bridge → β-side bridge → β-
side non-negativity helpers → β-polynomial bridge.

The cycle 347 task results explicitly recommend a **scoping cycle**
(over an implementation cycle). Per the cycle 200/201 rollback
precedent, multi-cycle work must be scoped *before* sorry-first
scaffolds are attempted, and the β-side derivation from
`IsStable + IsConsistent` alone is genuine investigation work
(textbook characterization is non-standard).

**Cycle 348 deliverable**: a Markdown scoping doc at
`.prover-state/issues/eq422a_eta_phase_D_prime_step_2_scoping.md`
laying out the multi-cycle plan for deriving `0 ≤ coef_β(M)` from
`IsStable + IsConsistent` alone — which would eliminate the
explicit `hβ_nn` hypothesis from cycle 345's
`Eq422a_at_vertex_eta_eq_of_stable_preconsistent`.

**No Lean code this cycle.** Mirror the cycle 260
(`lem_310B_plan.md`), cycle 336 (`def_422B_path.md`), and cycle 180
(`lem_441A_phase_C_scoping.md`) scoping templates.

## B. Priorities (in order)

### P1 — Write the Phase D′ Step 2 scoping doc (REQUIRED)

Create `.prover-state/issues/eq422a_eta_phase_D_prime_step_2_scoping.md`
with the following structure (≥200 lines, Markdown only):

#### §1 — Textbook source

Quote the relevant Butcher passages. Read `extraction/raw_text/ch04.txt`
in the §403–§451 region to identify whether there is a *direct*
textbook characterization of `Σ_{i:Fin (k+1)} i · M.β i ≥ 0` under
`IsStable + IsConsistent`. Key questions:

* Does Butcher §403 (Dahlquist stability) characterize the β-polynomial?
* Does Butcher §441 (Dahlquist barrier) state β-side conditions?
* Does the (404b) consistency equation
  `Σ_{i:Fin k} (i+1)·α_{i+1} = Σ_{i:Fin (k+1)} β_i` provide an
  algebraic route?

Quote ≥3 relevant paragraphs verbatim with line-number citations
from ch04.txt.

#### §2 — What we need to prove

State the precise target theorem:

```lean
theorem coef_β_nonneg_of_stable_consistent
    {k : ℕ} (M : LinearMultistepMethod k) (hk : 0 < k)
    (hStable : M.IsStable) (hCons : M.IsConsistent) :
    0 ≤ coef_β M
```

equivalently (via cycle 347's bridge):

```lean
theorem βPoly_deriv_eval_one_nonneg_of_stable_consistent
    {k : ℕ} (M : LinearMultistepMethod k) (hk : 0 < k)
    (hStable : M.IsStable) (hCons : M.IsConsistent) :
    0 ≤ (Section410.βPoly M).derivative.eval 1
```

#### §3 — Existing infrastructure inventory

List the Lean symbols at HEAD that this work can consume. Verify each
exists by `grep -n` or `lean_local_search`:

* `Section422.coef_β` (cycle 340)
* `Section422.coef_β_eq_βPoly_deriv_at_one` (cycle 347)
* `Section422.coef_β_nonneg_of_β_nonneg` (cycle 346 — the
  pointwise-`β_i ≥ 0` premise version that this work aims to
  eliminate)
* `Section410.βPoly` (cycle 73)
* `Section410.βPoly_natDegree_le` (cycle 73)
* `Section410.βPoly_explicitEuler` (cycle 73)
* `Section404.LinearMultistepMethod.IsStable` (Section404)
* `Section404.LinearMultistepMethod.IsConsistent` (Section404)
* `Section404.LinearMultistepMethod.SatisfiesEq404b` (Section404)
* `Section451.bdf2LMM_isStable` (cycle 346)
* `Section451.bdf2LMM_isConsistent` (existing)
* α-side template at `Section441.lean`:
  - `ρPoly_no_real_root_gt_one` (cycle 175)
  - `ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent` (cycle 176)
  - `ρPoly_pos_on_Ioi_one` (cycle 177)
  - `ρPoly_deriv_eval_one_pos_of_stable_preconsistent` (cycle 178)
  - `aPoly_coeff_one_pos_of_stable_preconsistent` (cycle 179)

#### §4 — Candidate routings

Document at least **three** candidate proof routes, with risk
assessment for each:

**Route A — α-side template port**: Mirror the cycle 175–178 chain
on the β-side. Requires:
- A β-side analog of "ρ has no real root > 1" — but `βPoly` may
  *not* have leading coefficient 1, so the boundedness argument
  differs.
- A β-side analog of "ρ'(1) ≠ 0" — Butcher §403/§441 may not
  guarantee this.
- A β-side analog of "ρ > 0 on (1, ∞)" — depends on leading
  coefficient sign.

**Route B — Consistency-driven**: Use (404b) directly:
`Σ_{i:Fin k} (i+1)·α_{i+1} = Σ_{i:Fin (k+1)} β_i = sum_β`. Combine
with `coef_α + coef_β = sum_β + coef_β` and cycle 344's
`coef_α > 0`. Pros: short. Cons: shows `coef_α + coef_β` non-zero,
not `coef_β` non-negative individually.

**Route C — Stability-polynomial argument**: Stability of an LMM is
typically characterized by *both* `ρ` and `σ` (the σ-polynomial in
Butcher notation = `βPoly` in our notation). For Dahlquist-stable
methods, the "boundary locus" `R(z) = σ(z)/ρ(z)` analysis may give
a direct sign condition on β-side derivatives. Pros: textbook-direct
if §403 has this. Cons: may require complex-analytic infrastructure
(Schur reduction, Routh-Hurwitz).

For each route, estimate:
* LOC budget (~50, ~150, ~300+).
* Cycles required (1–5).
* Mathlib hook completeness.
* Risk of dead-end.

#### §5 — Phase decomposition

Decompose the chosen route(s) into single-cycle phases. Each phase
must:
* Ship axiom-clean (no sorries).
* Have a concrete LOC budget (~80–200 LOC).
* Cite specific Mathlib hooks (verified by `lean_local_search`).
* Include a non-vacuity witness target (`bdf2LMM`, `explicitEulerLMM`,
  or a fresh `adamsBashforth2LMM` if needed).

Recommended baseline phasing (subject to revision based on §4):

* **Phase D′.2.0** (1 cycle, scoping continuation if textbook
  reading reveals a non-obvious route): refine the chosen route.
* **Phase D′.2.1** (1–2 cycles): build βPoly analogs of the α-side
  Section441 helpers actually needed by the chosen route.
* **Phase D′.2.2** (1 cycle): close
  `coef_β_nonneg_of_stable_consistent`.
* **Phase D′.2.3** (1 cycle): ship the unconditional corollary
  `Eq422a_at_vertex_eta_eq_of_stable_consistent` dropping cycle
  345's `hβ_nn` hypothesis.

#### §6 — Risk assessment

* **R1**: textbook may not provide a clean direct characterization;
  β-side may need novel formalization-side derivation. Mitigation:
  spend cycle 349's first hour reading ch04.txt before committing
  to phasing.
* **R2**: Route A requires the leading coefficient of `βPoly` to be
  sign-definite. Verify via `Section410.βPoly` definition: it's
  `Σ_{i:Fin (k+1)} M.β i · X^i`, so leading coefficient is `M.β k`.
  This is *not* fixed by `IsConsistent` or `IsStable` — could be
  zero (e.g. explicit LMMs have `β k = 0`) or negative. Route A
  may not generalize cleanly.
* **R3**: GPFS-slow files: cycle 182 documented Section441 timeouts.
  Section422 has compiled cleanly throughout cycles 336–347 (≤300s
  warm rebuilds), so Section422 is not affected. Section410
  similarly clean.
* **R4**: Faithfulness divergence risk: if no textbook route exists,
  defining `coef_β ≥ 0` as a *derived* statement requires careful
  documentation per cycle 250's `alphaWeight` precedent. Avoid
  definition smuggling.

#### §7 — Cycle 349 entry point

Concrete deliverable for the cycle 349 worker:

1. (~30 min) Read `extraction/raw_text/ch04.txt` §403, §441, §451
   in the regions identified by §1 of this scoping doc. Annotate
   with line numbers.
2. (~60 min) Verify Mathlib hooks for the chosen route via
   `lean_local_search`. Look for: `Polynomial.derivative_eval`,
   `Polynomial.coeff_natDegree`, `Polynomial.leadingCoeff_eq`,
   real-analytic `Polynomial.continuousOn`, `IVT` variants.
3. (~rest of cycle) Begin Phase D′.2.1 if Route confidence is high;
   else iterate on this scoping doc with updated route assessment.

#### §8 — Cross-references

* `.prover-state/issues/def_422B_path.md` — parent multi-phase plan
  for `def:422B`.
* `.prover-state/issues/lem_441A_phase_C_scoping.md` — sibling
  scoping template (cycle 180; α-side `aᵢ ≥ 0` analog).
* `.prover-state/issues/lem_441A_alpha_prime_negative.md` —
  cycle 174–179 α-side closure (template for β-side).
* `OpenMath/Chapter4/Section410.lean:103` — `βPoly` definition.
* `OpenMath/Chapter4/Section422.lean:957` — cycle 347's bridge.
* `OpenMath/Chapter4/Section441.lean:767, 913` — α-side
  ρ'(1) > 0 and a₁ > 0 closures (template targets).

### P2 — DO NOT ship Lean code this cycle

This is a scoping-only cycle. The §422 implementation streak is
12 cycles long; an additional implementation cycle without a
phased plan risks the cycle 200/201 rollback pattern (sorry-first
scaffold without single-cycle close). Defer all Lean changes to
cycle 349+ once Phase D′ Step 2 has a concrete phasing.

### P3 — `lean_status.json` and `plan.md` — NOTHING THIS CYCLE

Both files are correct at HEAD. `def:422B` is `partial`, all Phase
D′ Step 1 work is recorded. Do not touch unless the scoping doc
warrants a status field update — which it does not (scoping does
not change formalization status).

## C. What NOT to try

* **Do NOT attempt `coef_β_nonneg_of_stable_consistent` directly.**
  The textbook route is unclear; cycle 347 task results explicitly
  flag this as needing 2–3 cycles of investigation before
  scaffolding. Implementation without scoping risks rollback.

* **Do NOT extend cycle 345/346/347 to additional β-side helpers.**
  We have enough cycle-340 / 344 / 346 / 347 infrastructure to
  scope the route. Adding more helpers ad-hoc without a phasing
  plan is the pattern that caused the cycle 200/201 rollback.

* **Do NOT pivot to a fresh entity.** The cycle 347 recommendation
  is scoping, not pivoting. The 12-cycle §422 investment compounds
  best with continued §422 scoping work — option C in the cycle
  347 task results is a fallback, not the primary choice.

* **Do NOT introduce sorries.** Section422 has been sorry-clean for
  12 cycles. Maintain this.

* **Do NOT modify `scripts/autonomous_loop.py` or any prompt-builder
  infrastructure.** Per the standing
  `tautology_scanner_false_positives.md` and
  `phantom_commit_verdict_pattern.md` issues, scanner / supervisor
  bugs are loop-maintainer territory.

* **Do NOT raise `maxHeartbeats` above 200000.** Not applicable this
  cycle (no Lean code), but standing rule.

* **Do NOT attempt Section441 compile.** GPFS timeouts persist
  (43+ consecutive since cycle 182, per
  `cycle_182_gpfs_slowness.md`). Skip per established protocol.

* **Do NOT touch `extraction/raw_text/` or
  `extraction/formalization_data/entities/`.** Both are
  regenerated; read-only for scoping. The scoping doc can quote
  `extraction/raw_text/ch04.txt` but must not edit it.

* **Do NOT submit Aristotle jobs this cycle.** No pending jobs;
  scoping work doesn't benefit from Aristotle compute.

* **Do NOT exceed the 200-line minimum loosely.** Be specific and
  substantive in each section — the cycle 200/201 rollback
  precedent was caused by *insufficiently* scoped multi-cycle
  work. Match the cycle 180 / 260 / 336 template depth.

## D. Verification

The cycle 348 deliverable verifies if:

1. `.prover-state/issues/eq422a_eta_phase_D_prime_step_2_scoping.md`
   exists at HEAD.
2. The file has ≥200 lines of Markdown.
3. The file contains all 8 sections (§1 through §8) listed in P1.
4. Each section is substantive (no empty placeholder content).
5. §1 quotes at least 3 lines from `extraction/raw_text/ch04.txt`
   with line-number citations.
6. §3 lists ≥10 existing Lean symbols verified to exist at HEAD.
7. §4 documents at least 3 candidate routes with risk assessment.
8. §5 phase decomposition has at least 3 phases with LOC budgets.
9. §7 specifies a concrete cycle 349 entry point.
10. `git diff` shows only the new scoping file (plus standard
    `.prover-state/` heartbeat/history updates).
11. `grep -c sorry OpenMath/` returns the same count as cycle 347
    (zero new sorries introduced).

## E. Faithfulness check (no Lean code, but document the rationale)

Since cycle 348 ships no Lean theorems, the standard Pre-Commit
Faithfulness Checklist does not apply. The scoping doc itself
must:

* Avoid definition smuggling in its proposed routes (per the cycle
  250 `alphaWeight` precedent).
* Cite textbook material accurately (verbatim quotes with line
  numbers).
* Flag any divergence risks in §6.

## F. Task results template

Write `.prover-state/task_results/cycle_348.md` documenting:

* Worked on: Phase D′ Step 2 scoping for `def:422B`.
* Approach: scoping-doc-only cycle per cycle 347 task results
  recommendation, with the structure detailed in P1 above.
* Result: SUCCESS / PARTIAL — scoping doc shipped at
  `.prover-state/issues/eq422a_eta_phase_D_prime_step_2_scoping.md`.
* Faithfulness check: N/A (no Lean code).
* Dead ends: any textbook routes ruled out during §1 reading.
* Discovery: any unexpected findings about β-side characterization.
* Suggested next approach: cycle 349 enters Phase D′.2.0 or D′.2.1
  per the §5/§7 phasing in the new scoping doc.

## G. Why this strategy

Per CLAUDE.md and the cycle 347 task results:

* **CLAUDE.md "Sorry-first (ABSOLUTE RULE)"** — does not apply to a
  scoping cycle (no Lean code).
* **CLAUDE.md "A cycle with zero changes is unacceptable"** —
  satisfied by the new scoping doc (~200+ lines of new content).
* **CLAUDE.md "If stuck on a sorry, write a structured issue file"**
  — analogous: when about to start multi-cycle work, write the
  scoping doc first.
* **Cycle 200/201 rollback precedent** — multi-cycle work without
  phased scoping rolls back. The Phase D′ Step 2 derivation is
  genuinely multi-cycle (textbook characterization unclear); scoping
  is mandatory before implementation.
* **Cycle 260 / 336 / 180 scoping precedent** — three prior scoping
  cycles produced concrete, immediately-actionable plans for
  multi-cycle work. Match that template structurally.
* **Cycle 347 task results §"Suggested next approach"** — explicitly
  recommends scoping for cycle 348 (option A).
