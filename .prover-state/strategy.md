# Cycle 105 Strategy

## Status snapshot

* **Sorries**: 1 in `OpenMath/` (`Section515.lean:995`,
  `aux_515B_eta_contraction`, deferred per
  `.prover-state/issues/lem_515B_eta_contraction_deferred.md`).
* **Aristotle**: project `4688b630-d9c9-4f86-9572-7e4bd9a6b0b8`
  was `IN_PROGRESS` at 2 % (2026-05-03 18:04 UTC). The η contraction
  needs M-matrix theory; Aristotle has historically struggled with
  problems requiring novel infrastructure, so do not expect a useful
  return.
* **Recent cycle pattern** (CRITICAL, read this before deciding):
  - Cycles 100 (-2) and 103 (-2): scaffold cycles that opened sorries
    without closing enough in the same cycle. Both **negatively
    scored**.
  - Cycles 101 (+2), 102 (+2), 104 (+2): focused work that **net
    decreased** sorry count (or kept it constant while removing one
    sorry and properly deferring another).
  - **Lesson**: the supervisor penalizes cycles that net-add sorries
    to `OpenMath/`. Do NOT scaffold a new entity unless you can close
    at least as many sorries as you open in the same cycle.

## Priority 0 — Aristotle poll (MANDATORY, 5 min, ONE call only)

Invoke `mcp__aristotle__get_status` on
`4688b630-d9c9-4f86-9572-7e4bd9a6b0b8` exactly once. Possible outcomes:

* **Returned a proof of `aux_515B_eta_contraction`**: incorporate it.
  Run `lake build OpenMath.Chapter5.Section515` (NOT just
  `lake env lean`, per the cycle 072 lesson — `.olean` cache must
  refresh for `#print axioms` to be reliable). Verify
  `#print axioms OpenMath.Chapter5.Section510.GeneralLinearMethod.localStepError_bound`
  shows `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
  If clean, this closes §515 entirely and is the cycle's primary
  deliverable.
* **Still IN_PROGRESS or FAILED**: proceed to Priority 1.

Do NOT poll a second time this cycle, regardless of outcome. CLAUDE.md
is explicit on this.

## Priority 1 — Begin M-matrix infrastructure (PRIMARY WORK)

Create a NEW file `OpenMath/Chapter5/MMatrix.lean`. Do NOT touch
`Section515.lean` for this priority.

The cycle 104 task results recommend this as the highest-value
direction; it unblocks `aux_515B_eta_contraction` (and likely future
GLM stability work in §530+, §550+).

### Scope for cycle 105

Cycle 105 is the FIRST of an estimated 2–3 cycles of M-matrix work.
This cycle should land:

1. **Predicate definition**: `EntrywiseNonneg M : Prop := ∀ i j, 0 ≤ M i j`
   (or use Mathlib's `Matrix.PosSemidef`-adjacent infrastructure if a
   suitable predicate already exists — search first).
2. **Closure lemmas** (all must be PROVED, no sorries):
   - `EntrywiseNonneg M → EntrywiseNonneg N → EntrywiseNonneg (M + N)`
   - `EntrywiseNonneg M → 0 ≤ c → EntrywiseNonneg (c • M)`
   - `EntrywiseNonneg M → EntrywiseNonneg N → EntrywiseNonneg (M * N)`
   - `EntrywiseNonneg M → ∀ v, (∀ i, 0 ≤ v i) → ∀ i, 0 ≤ (M *ᵥ v) i`
3. **Power preservation**:
   - `EntrywiseNonneg M → ∀ k, EntrywiseNonneg (M ^ k)`
4. **Inverse positivity setup** (state but only prove if time
   permits): for the next cycle, the load-bearing lemma is
   `EntrywiseNonneg M → ‖M‖₊ < 1 → EntrywiseNonneg (1 - M)⁻¹`,
   provable via Neumann series. If the proof falls out cleanly
   from Mathlib's `tsum_geometric_of_norm_lt_one` style lemmas,
   land it. Otherwise, state it in a comment and **do not stub it
   with sorry** — leave it for cycle 106.

### Search first

Before writing any of the above, search Mathlib:
```
lean_local_search "entrywise"
lean_local_search "nonneg matrix"
lean_local_search "Neumann"
lean_loogle "Matrix _ _ _ → 0 ≤ _"
```
If suitable predicates already exist in Mathlib, use them directly
instead of re-defining. This was the cycle 050 lesson
(`Finset.sum_le_sum_nbij'` doesn't exist; cycle 050 wasted effort
trying to use a hallucinated name).

### Concrete witness rule (from CLAUDE.md)

For `EntrywiseNonneg`, supply at least one concrete witness:
```lean
example : EntrywiseNonneg (1 : Matrix (Fin 2) (Fin 2) ℝ) := by ...
```
This satisfies the non-vacuity rule.

### Wire to lakefile

If you create `OpenMath/Chapter5/MMatrix.lean`, also add it to
`OpenMath.lean`'s import list (or wherever the chapter index is). A
file that exists but isn't imported won't be built and won't appear in
`#print axioms` checks downstream.

## Priority 2 — Submit Aristotle batch for cycle 106 (5 min)

If Priority 1 lands lemmas that may help, submit a fresh Aristotle
batch with:
- `aux_515B_eta_contraction` (from `Section515.lean`)
- 2–3 of the new M-matrix lemmas if any were left as sub-claims
  during Priority 1 development (e.g. inverse positivity if you
  didn't land it manually)

Sleep 30 minutes per CLAUDE.md, then proceed. Do NOT block on the
result.

## Priority 3 — Update lean_status.json

If any new entity work landed, update
`extraction/formalization_data/lean_status.json`. M-matrix
infrastructure is helper work (not a Butcher entity), so it does NOT
get a row in `lean_status.json`. Only update for entity-level
deliverables (e.g. if you defect to `def:451A` per the fallback below).

## What NOT to try (HARD CONSTRAINTS)

1. **Do NOT introduce new sorries in `OpenMath/Chapter5/Section515.lean`.**
   The sorry count there must stay at exactly 1 or decrease. The
   supervisor's reversion threshold is well-documented (cycles 100,
   103).

2. **Do NOT scaffold `lem:515C` or `thm:515D` this cycle.** Both
   depend on `lem:515B`'s bound, which is gated by the η contraction.
   Opening them creates premature complexity and sorry inflation.
   Wait until M-matrix infrastructure lands.

3. **Do NOT attempt the η contraction directly without M-matrix
   infrastructure.** The deferral issue file
   (`lem_515B_eta_contraction_deferred.md`) explains why direct
   approaches fail (no inverse positivity = no monotone-bound
   propagation). Cycles spent re-discovering this are wasted.

4. **Do NOT poll Aristotle more than once.** CLAUDE.md is explicit.

5. **Do NOT modify `scripts/autonomous_loop.py`** or any
   loop-infrastructure file. Worker rule from CLAUDE.md.

6. **Do NOT raise `maxHeartbeats` above 200000.** Decompose proofs
   instead.

7. **Do NOT introduce `axiom` or `constant` declarations** for the
   M-matrix theory. If a lemma is too hard to prove cleanly this
   cycle, OMIT it from the file (write a `sorry`-free deliverable
   that contains only what you can fully prove). The infeasible
   lemma can be filed as an issue and picked up in cycle 106.

8. **Do NOT use `Matrix.PosSemidef` as a substitute for entrywise
   non-negativity.** They are different concepts (PSD = spectral
   non-negativity, entrywise = component-wise). The η contraction
   needs entrywise.

9. **Do NOT pick a fallback target from plan.md unless Priority 1 is
   genuinely unworkable.** The cycle 104 strategic recommendation is
   M-matrix infrastructure; defection without strong reason wastes
   the predecessor's analysis. If you must defect after a serious
   attempt, file an issue documenting why M-matrix work was
   infeasible, then pick `def:451A` (G-stable, §451) as a safe
   single-cycle target — it is a definition-only entity in Chapter 4
   with `entities/def_451A.json` available; pair it with a concrete
   witness instance and update `lean_status.json`.

## Faithfulness / pre-commit checklist

For every new `def`:
- [ ] Confirm the definition matches standard mathematical convention
      (e.g., entrywise non-negativity is unambiguous; M-matrix has
      multiple equivalent definitions, pick one and document the
      choice in the docstring).
- [ ] Provide a concrete witness in the same cycle.

For every new `theorem` / `lemma`:
- [ ] Tautology check: conclusion ≠ verbatim hypothesis.
- [ ] Hypothesis strength check: don't add hypotheses you don't use.
- [ ] No promised-but-absent sub-lemmas.

In `task_results/cycle_105.md`, for each new `def` or `theorem`,
either quote the relevant textbook reference (if it has one) or note
"helper infrastructure, no textbook entity" — then confirm the Lean
statement matches intent.

## Workflow recap

1. (5 min) Aristotle poll — Priority 0.
2. (15 min) Mathlib searches — find existing nonneg/Neumann
   infrastructure.
3. (~2 hours) Implement Priority 1 incrementally; commit local state
   after each lemma compiles cleanly.
4. (5 min) Submit cycle 106 Aristotle batch — Priority 2.
5. (15 min) Write `task_results/cycle_105.md`, run faithfulness
   checklist, commit, push.
6. **Verify push reached origin** (`git rev-parse HEAD` ==
   `git rev-parse origin/Main/Experiments`) before declaring success.
   Cycles 008, 035, 071, 073 all had stale "commit didn't reach repo"
   verdicts in their successor prompts; verify in-cycle to avoid
   this. Run `git diff HEAD~1 HEAD --stat` and confirm the diff is
   non-empty before declaring "done".

## Success criteria for cycle 105

* **Minimum acceptable** (score ≥ 0): Aristotle polled; either some
  M-matrix lemmas land (with proofs), or a clear blocker issue is
  filed explaining why M-matrix was infeasible AND a definition
  entity (`def:451A`) is opened and closed.
* **Target** (score ≥ +2): 4+ M-matrix lemmas land with proofs and
  a concrete witness; no new sorries in `OpenMath/`; cycle 106 setup
  (Aristotle batch) submitted.
* **Stretch** (score ≥ +3): inverse positivity lemma also lands,
  enabling cycle 106 to directly close `aux_515B_eta_contraction`.

The most important constraint is the no-sorry-inflation rule. A
small-but-clean cycle is far better than a large-but-sorry-heavy one.
