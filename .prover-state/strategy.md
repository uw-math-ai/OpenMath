# Cycle 336 strategy — Pivot break: scoping doc for `def:422B` + small Phase 0 deliverable

**Cycle goal**: Break the 14-cycle §344 streak (cycles 322–335) cleanly by
opening a new §422 (Chapter 4 LMM ↔ §383 group bridge) work track via a
multi-phase scoping document, plus a small auxiliary Lean ship that
verifies the prerequisite infrastructure is healthy without committing
to multi-cycle work this cycle.

The cycle 335 P2 menu (`.prover-state/issues/cycle_336_pivot_options.md`)
listed four candidates (B `thm:302A`, A `def:422B`, C `thm:302B`, D
`thm:384A` partial). After review (§A below): all four have hidden
multi-cycle complications. The cleanest cycle-336 contribution is a
**scoping document for `def:422B`** (modelled on `lem_310B_plan.md`,
`lem_441A_phase_C_scoping.md`, `def_530B_scaffold_strategy.md`), plus
an axiom-clean Phase 0 Lean deliverable confirming the
`LinearMultistepMethod ↔ PhiEquivalent.setoidSigma` prerequisite stack
is wired up.

---

## §A — Why the other cycle 335 P2 candidates were ruled out

Do **NOT** spend cycle 336 re-debating this. The audit below is the
result of cycle 336's planner analysis; treat it as decided.

### Candidate B — `thm:302A` (Some combinatorial questions)

* **Hidden blocker**: per
  `.prover-state/issues/cycle_250_strategy_alpha_definition_error.md`,
  `RootedTree.alphaWeight` (shipped cycle 250) is **defined as the
  closed-form RHS** `r(t)! / (σ(t) · γ(t))`, NOT as the labelling
  count. To honestly formalise thm:302A, we need a separate
  `alphaCount : RootedTree → ℕ` defined as the count of constrained
  labellings, then prove `(alphaCount t : ℝ) = alphaWeight t`.
* The `alphaCount` infrastructure requires the **strengthened**
  `TreeAutomorphism` predicate that cycle 263 deferred. Cycle 263
  shipped a *weakened* root-fixing-only `TreeAutomorphism` to dodge the
  `feedback_rootedtree_nested_induction.md` mutual-recursion pitfall;
  per cycle 263 update in `lem_310B_plan.md` Phase A.2 closure, the
  Setoid is **coarser** than Butcher's quotient — would over-count.
* **Decision**: multi-cycle (Phase A.3 of `lem_310B_plan.md` first
  — strengthen `TreeAutomorphism` + orbit-count theorem). Defer.

### Candidate A — `def:422B` (underlying one-step method, LMM ↔ G_1)

* **Surface claim** (cycle 335 P2 doc): "1–2 cycles, builds on §383
  `instGroup_phi` and `Φ` already done."
* **Reality** (after reading entity JSON):
  > "Corresponding to a linear multistep method [α, β], the member of
  > G_1 represents the 'underlying one-step method'."
  The textbook *names* a term (the underlying one-step method) that
  the surrounding §422 prose constructs **inductively on the order of
  trees** via equation (422a). The construction is the load-bearing
  content of `thm:422A` (also unformalized) and Butcher §422.
* def:422B as a standalone `def` without the construction is either
  (i) **definition smuggling** (defining "underlying one-step method"
  as "the thing satisfying eq (422a)" without producing it), or (ii)
  **the construction itself** (multi-cycle tree-recursive `η` ship).
* **Decision**: multi-cycle. → Scope as `def_422B_path.md` this cycle;
  ship Phase 0 prerequisite verification only.

### Candidate C — `thm:302B` (Rooted tree generating function identity)

* Requires `PowerSeries` / `MvPowerSeries` infrastructure for the
  formal `∏ (1 − x^k)^(−θ_k)` identity. Multi-cycle per the cycle 335
  P2 doc's own assessment ("3–5 cycles minimum"). Skip.

### Candidate D — `thm:384A` (Φ as group homomorphism §382 → §383)

* Per plan.md cycle 239 line: blocked on `Equivalent → PhiEquivalent`
  direction, which is one of the **two remaining deferred directions
  in thm:381H** (per `thm_381H_deferred.md` cycle 208 update). The
  closure path is Banach-fixed-point machinery (multi-cycle, started
  cycle 201 P2 with `RKStageMap` foundation but not connected through
  to the bridge).
* **Decision**: blocked on multi-cycle Banach work. Skip.

---

## §B — Cycle 336 deliverables (P0 → P3)

### P0 (5 min, mandatory) — verify cycle 335 ship is healthy

Run the cycle 335 verification commands one time:

```bash
git log -1 --format='%H %s'
# Expected: 8c32d4f Cycle 335 — §344 Phase D.14: Lobatto III `s = 3` direct-form `RKTableau` + `SatisfiesC 2` certificate shipped.

wc -l OpenMath/Chapter3/Section344.lean
# Expected: ~2670 LOC (cycle 335 added ~83 LOC over cycle 334's 2587 LOC)

grep -c sorry OpenMath/Chapter3/Section344.lean
# Expected: 0

lake env lean OpenMath/Chapter3/Section344.lean
# Expected: clean exit
```

If any check fails, escalate as cycle 335 regression (file a 1-line
`task_results/cycle_336.md` flagging the regression and stop). All
checks should pass per cycle 335 task results.

### P1 (mandatory, primary deliverable) — write `def_422B_path.md` scoping doc

Create **`.prover-state/issues/def_422B_path.md`** following the
`lem_310B_plan.md` / `lem_441A_phase_C_scoping.md` template. Required
sections (mirror the precedent docs section-by-section):

1. **Status header**. State this is a scoping doc, not a Lean
   deliverable; cite cycle 336 as origin; cite the cycle 335 P2 menu
   (`cycle_336_pivot_options.md`) as predecessor.
2. **§1 Textbook statement (verbatim)**. Quote from
   `extraction/formalization_data/entities/def_422B.json`'s
   `statement_text` + `context_latex`. Include equation (422a) and
   the (422b) reference. Cite Butcher 3rd ed. §422 p. 359.
3. **§2 Distilled mathematical content**. Identify what `η : RootedTree
   → ℝ` is: an element of `G_1 = Quotient PhiEquivalent.setoidSigma`
   satisfying eq (422a) for the LMM `[α, β]`. The "inductive
   construction on tree order" — for each tree `t`, `η(t)` is
   determined by lower-order trees via (422a), using the operator `D`
   (related to differentiation / tree-grafting; clarify exactly which
   in the doc).
4. **§3 Project-hook inventory** (verified at HEAD — `grep -n` /
   `lean_local_search` results required). Cover at minimum:
   * `LinearMultistepMethod k` (Chapter 4 §404, cycle 35-onwards;
     verify with `grep -n LinearMultistepMethod OpenMath/Chapter4/Section404.lean`)
   * `LinearMultistepMethod.{IsPreconsistent,IsStable,IsConsistent}`
     (Chapter 4 §404–§406, ensure they exist for the "preconsistent
     and stable" hypothesis of (422a)'s context)
   * `Quotient PhiEquivalent.setoidSigma` + `instGroup_phi` (cycle 236)
   * `composeQ_phi` (cycle 232)
   * `elementaryWeightQ_phi` (cycle 239)
   * `RootedTree`, `order`, `RootedTree.tau_values` (§310 cluster)
5. **§4 Gap inventory**. Identify infrastructure missing for the
   construction. At minimum:
   * The "operator D" on trees (or on `Quotient PhiEquivalent.setoidSigma`)
     — need to define `D : G_1 → G_1` or `D : RootedTree → RootedTree
     → ℝ`-style action. Verify whether Butcher's `D` is
     tree-substitution / tree-grafting / multiplication by `τ`.
   * Recursive solver for eq (422a): for each tree `t`, solve a linear
     equation in `η(t)` given `η(t')` for `t'` with smaller order.
     This is the substantive multi-cycle content.
   * `η^(-k)` composition in `G_1` (k-fold inverse-power). Available
     via `instGroup_phi.zpow` once the integer-power API is wired up;
     verify Mathlib hook.
6. **§5 Phase decomposition**. 4–6 phases, each ≤2 cycles. Suggested
   skeleton (refine in the doc; LOC budgets are estimates):
   * **Phase A** (1–2 cycles): `D : G_1 → G_1` operator definition.
     Includes the tree-grafting / multiplication-by-τ choice and
     non-vacuity at `τ`.
   * **Phase B** (1 cycle): `inverseQ_phi.zpow` integer-power API
     wrapping cycle 236's `inverseQ_phi`. Verify Mathlib `Group.zpow`
     bridges cleanly.
   * **Phase C** (2–3 cycles): the recursive (422a) solver — for an
     LMM `[α, β]` and order-`n` tree `t`, solve for `η(t)` in terms
     of `η(t')` for `r(t') < r(t)`. State as `noncomputable def
     underlyingOneStepMethod_aux : LinearMultistepMethod k → RootedTree
     → ℝ` with well-founded recursion on `RootedTree.order`.
   * **Phase D** (1 cycle): lift to `Quotient PhiEquivalent.setoidSigma`
     via the function `RootedTree → ℝ` → `Quotient PhiEquivalent.setoidSigma`
     bridge (verify this bridge exists — likely needs a fresh helper
     converting an arbitrary `RootedTree → ℝ` function to a `G_1`
     element).
   * **Phase E** (1 cycle): close `def:422B` as `noncomputable def
     LinearMultistepMethod.underlyingOneStepMethod : Quotient
     PhiEquivalent.setoidSigma`. Non-vacuity: backward Euler LMM
     (cycle 142's `backwardEulerGLM` analogue, or §404's explicit
     Euler LMM if present), showing the underlying one-step method is
     the corresponding Runge–Kutta method.
   * **Phase F** (optional, 1 cycle): connect to `thm:422A` (the
     existence proof Butcher gives) and `thm:422C` (convergence).
7. **§6 Risk assessment**. Per-phase LOC budget, Mathlib hook
   confidence, Aristotle suitability. Total estimate: 6–10 cycles.
8. **§7 Cycle 337 entry point**. Recommend Phase A as cycle 337's
   target. Sketch the concrete Lean signature for Phase A's
   deliverable (the `D` operator).
9. **§8 Cross-references**. Link to:
   * `.prover-state/issues/thm_382A_path.md` (§382 group construction,
     cycle 215–222 multi-cycle precedent)
   * `.prover-state/issues/cycle_336_pivot_options.md` (cycle 335 P2
     menu)
   * `.prover-state/issues/lem_310B_plan.md` (multi-phase scoping
     template)
   * `.prover-state/issues/lem_441A_phase_C_scoping.md` (multi-phase
     scoping template)

**LOC budget for this doc**: 200–400 lines of Markdown. Do NOT inline
Lean code in the scoping doc beyond signature sketches in §7 — proof
recipes belong in the actual phase cycles. Cite section / line numbers
when referencing existing infrastructure.

### P2 (mandatory, small Phase 0 Lean deliverable) — wire-up sanity ship

Ship a **5–20 LOC axiom-clean** sanity theorem that confirms the
`LinearMultistepMethod` ↔ `Quotient PhiEquivalent.setoidSigma`
prerequisite stack is healthy. Two options (pick whichever compiles
cleaner on first attempt):

**Option P2.α** — `LinearMultistepMethod` exists and is non-vacuous in
the Phase 0 sense:

```lean
-- in OpenMath/Chapter4/Section422.lean (new file) OR OpenMath/Chapter4/Section404.lean
namespace OpenMath.Chapter4.Section422

/-- def:422B Phase 0 sanity: the §383 `PhiEquivalent` quotient group
exists, and every `LinearMultistepMethod k` will eventually map into
it via the (multi-cycle) `underlyingOneStepMethod` construction
scoped at `.prover-state/issues/def_422B_path.md`. This Phase 0
theorem only confirms the target type is non-empty (using cycle 236's
`instGroup_phi` instance and cycle 222's `paddedEuler` witness). -/
theorem underlyingOneStepMethod_target_nonempty :
    Nonempty (Quotient OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma.{0}) :=
  ⟨⟦⟨2, OpenMath.Chapter3.Section381.paddedEuler⟩⟧⟩

end OpenMath.Chapter4.Section422
```

Place in either a fresh `OpenMath/Chapter4/Section422.lean` (preferred
— signals new work track) or appended to `Section404.lean` (avoid;
cluttered file). If creating a new file, also update
`OpenMath/Chapter4.lean` aggregator.

**Option P2.β** — if Option P2.α hits Section381 import-cycle issues
(Chapter 4 importing Chapter 3 may already be in the import graph,
verify), fall back to a trivial sanity theorem inside `Section381.lean`
itself that references `LinearMultistepMethod` via a forward import:

```lean
-- append to OpenMath/Chapter3/Section381.lean only if Section404 imports cleanly
example : Nonempty (Quotient PhiEquivalent.setoidSigma.{0}) :=
  ⟨⟦⟨2, paddedEuler⟩⟧⟩
```

If even this fails, ship just the scoping doc (P1) — supervisor scoring
should still accept P1 as cycle deliverable per the
`lem_310B_plan.md` (cycle 260) and `lem_441A_phase_C_scoping.md`
(cycle 180) precedents (both were scoping-doc-only cycles).

**Axiom-clean target**: `#print axioms` must return
`[propext, Classical.choice, Quot.sound]` only. The example version
uses no axioms.

### P3 (optional, only if P0–P2 close in <50% of cycle) — extend scoping coverage

If cycle budget remains after P0–P2 ship, optionally extend the
scoping doc with:
* A **Mathlib hook audit appendix** for Phase B (`Group.zpow` integer
  power compatibility with cycle 236's `instGroup_phi`).
* Or, **read `thm:422A.json` and add a §9 to the scoping doc** outlining
  how `thm:422A` (the existence theorem) connects to `def:422B`'s
  construction.

**Do NOT** attempt any Phase A Lean work this cycle. Phase A is a
cycle 337+ deliverable.

---

## §C — What NOT to do

* **Do NOT continue the §344 ladder.** Cycle 335 was the final ship
  in the cycle 322–335 streak. Per cycle 335 task results: "no
  `butcherRadauIA_three`, no `butcherLobattoIIIA_four`, no further
  parking-orbit ships." Adding even one more §344 ship in cycle 336
  is a planner regression.

* **Do NOT attempt `thm:302A` as a direct `rfl` against `alphaWeight`.**
  Per `.prover-state/issues/cycle_250_strategy_alpha_definition_error.md`,
  `alphaWeight` is the closed-form RHS, NOT the labelling count. A
  one-line `theorem thm_302A : alphaWeight t = ... := rfl` is
  **definition smuggling** (CLAUDE.md pre-commit faithfulness
  checklist). The proper formalisation needs `alphaCount`
  infrastructure (multi-cycle).

* **Do NOT attempt `def:422B` as a `def` body this cycle.** The
  construction is multi-cycle (Phases A–E, est. 6–10 cycles per the
  scoping doc you're writing). A sorry-first scaffold would trigger
  the cycle 149/150 (def:530B) or cycle 200/201 (thm:381H) rollback
  pattern.

* **Do NOT attempt the `Equivalent → PhiEquivalent` direction for
  `thm:384A`.** Per `thm_381H_deferred.md` cycle 208 update, this is
  one of the two remaining deferred directions in thm:381H, blocked
  on Banach-fixed-point machinery (cycle 201 P2 started the
  `RKStageMap` foundation but did not connect through; multi-cycle).

* **Do NOT introduce sorries.** Section441's 43-cycle GPFS-timeout
  precedent (`cycle_182_gpfs_slowness.md`) and the 200/201 rollback
  precedent both teach: sorry-first scaffolds without a credible
  single-cycle close get rolled back at cost to the cycle. Phase 0
  ship (P2) must be axiom-clean.

* **Do NOT edit `scripts/autonomous_loop.py`.** Tautology-scanner
  false positives are loop-maintainer territory per
  `.prover-state/issues/tautology_scanner_false_positives.md`.

* **Do NOT raise `maxHeartbeats` above 200000** (CLAUDE.md rule).

* **Do NOT compile `OpenMath/Chapter4/Section441.lean`** — 43rd
  consecutive GPFS timeout was at cycle 239 (per
  `cycle_182_gpfs_slowness.md`). If the P2 deliverable accidentally
  triggers a Section441 transitive load, switch to P2.β (Section381
  example, much lighter import set).

---

## §D — Cycle 336 ship checklist

Before committing, the worker should verify:

1. `.prover-state/issues/def_422B_path.md` exists, 200–400 lines,
   covers all 8 required sections (P1 §B above).
2. The P2 Lean deliverable compiles cleanly:
   * `lake env lean <P2 file>` exits 0.
   * `#print axioms <P2 theorem-name>` returns
     `[propext, Classical.choice, Quot.sound]` only.
3. The aggregator builds: `lake env lean OpenMath/Chapter4.lean` (if
   Option P2.α used and Section422.lean was added) OR
   `lake env lean OpenMath/Chapter3.lean` (if Option P2.β).
4. Sorry count: 0 → 0 (must remain — cycle 336 is the 67th consecutive
   clean cycle since the cycle 201 rollback).
5. Tautology scanner returns 0 hits in any new file:
   `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' <new files>`
6. `lean_status.json`: `def:422B` row updated to
   `formalization_status: "partial"` ONLY if Option P2.α was shipped
   (the wire-up sanity theorem counts as Phase 0 partial closure);
   otherwise leave `def:422B` as `unformalized`.
7. `plan.md` Ch.4 §422 row: `[ ] def:422B` → `[~]` ONLY if
   `lean_status.json` row was updated to `partial`; otherwise no plan
   change.
8. `.prover-state/task_results/cycle_336.md` with the standard
   five sections (Worked on / Approach / Result / Faithfulness check /
   Dead ends / Discovery / Suggested next approach).

---

## §E — Suggested next cycle (337)

Per the def:422B scoping doc §7 entry point:

* **Cycle 337**: Phase A of `def_422B_path.md` — `D : G_1 → G_1`
  operator definition. Single-cycle target, ~80–120 LOC.
  Non-vacuity: `D ⟦⟨0, RKTableau.id⟩⟧ = ⟦⟨1, paddedEuler⟩⟧.something`
  or analogous tree-grafting witness.

* If Phase A turns out heavier than estimated, cycle 337 can defer
  to a `def_422B_path.md` revision (split Phase A into A.1 / A.2).

* Alternative cycle 337 pivot: if cycle 336 also wrote the §9 thm:422A
  appendix (P3 stretch), cycle 337 could pivot to thm:422A scoping
  instead and treat def:422B as a corollary in a later cycle.

---

## §F — Bottom-line directive for the cycle 336 worker

1. (5 min) Run §B.P0 verification commands. Confirm cycle 335 is
   healthy.
2. (90 min) Write `.prover-state/issues/def_422B_path.md` (P1) — the
   primary deliverable. Cite `extraction/formalization_data/entities/def_422B.json`
   verbatim in §1; cite existing project symbols with file:line in §3;
   propose 4–6 phases in §5; use `lem_310B_plan.md` and
   `lem_441A_phase_C_scoping.md` as structural templates.
3. (15 min) Ship P2 (Option P2.α preferred, P2.β fallback). One
   axiom-clean theorem confirming the target type is non-empty.
4. (10 min) Update `lean_status.json` + `plan.md` per §D.6–7. Write
   `task_results/cycle_336.md`. Commit and push.

Total: ~2 hours of focused work. **No §344 ship.** **No `thm:302A`
direct attempt.** **No `def:422B` body.** Just the scoping doc + tiny
sanity ship.
