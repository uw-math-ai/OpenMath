# Cycle 300 Strategy

## Context recap (cycle 299 close)

Last cycle shipped `butcherShiftedLegendre_eleven_roots` (n=11 empirical
anchor for `lem:342A` clause (342g)), axiom-clean. The empirical ladder
now stands at `n ∈ {1, 3, 5, 7, 9, 11}`. Section342.lean is ~3500 LOC,
0 sorries.

Aristotle project `5939f28b-c890-4b7f-be4f-ed0f31f0d0b5` (general (342g)
statement, citing all of (342a)–(342f) + cycle 292's
`butcherShiftedLegendre_orthogonal_to_lower_degree`) is in flight. Last
poll (cycle 299, 2026-05-15T23:56:34Z) returned `IN_PROGRESS` at 29%.
Growth trajectory: 16% → 19% → 25% → 28% → 29% across cycles 295–299.
**The +1pp gain in cycle 299 reset the stall counter to 0**; no
three-stall protocol is currently armed.

## Cycle 300 plan — three branches based on Aristotle poll

### Priority 0 (mandatory) — single Aristotle poll

Run **exactly one** `mcp__aristotle__get_status` call on project
`5939f28b-c890-4b7f-be4f-ed0f31f0d0b5`. Record:
- `status` (`COMPLETE` / `COMPLETE_WITH_ERRORS` / `IN_PROGRESS` / `FAILED`)
- `percent_complete`
- `last_updated` timestamp

Per CLAUDE.md: **do NOT re-poll within this cycle.** One poll, then proceed.

### Branch decision table

| Aristotle status | percent | Action |
|---|---|---|
| `COMPLETE` | 100% | **Branch A** — integrate general theorem (§A) |
| `COMPLETE_WITH_ERRORS` | any | **Branch A'** — integrate after fixing errors (§A') |
| `IN_PROGRESS`, ≥ 30% | up | **Branch B** — ship n=13 anchor (§B) |
| `IN_PROGRESS`, = 29% (flat) | flat #1 | **Branch B** — ship n=13 anchor; flag stall observation #1 |
| `IN_PROGRESS`, < 29% (regression) | down | **Branch C** — investigate; ship anchor as fallback |
| `FAILED` / cancelled | n/a | **Branch D** — pivot to manual closure plan (§D) |

### §A — Aristotle COMPLETE (Branch A)

If Aristotle returned a successful proof of the general (342g) theorem:

1. **Download the result** via `mcp__aristotle__download_result`.
2. **Inspect** the proof structure. Expected shape (per cycle 294
   submission): a sign-change-cardinality contradiction argument using
   `butcherShiftedLegendre_orthogonal_to_lower_degree` (cycle 292) on a
   product polynomial `Q := ∏ᵢ (X − xᵢ)` built from the sign-change zeros.
3. **Helper extraction**: if Aristotle's proof has multiple supporting
   lemmas, follow the cycle 281 / cycle 277 precedent and split helpers
   into a new file `OpenMath/Chapter3/Section342GZerosHelpers.lean`
   (analogous to `Section342NormSqHelpers.lean`). Section342.lean keeps
   only the headline + non-vacuity examples.
4. **Headline target**: a theorem of shape
   ```
   butcherShiftedLegendre_distinct_real_roots (n : ℕ) :
     ∃ (S : Finset ℝ), S.card = n ∧
       (∀ x ∈ S, x ∈ Set.Ioo (0 : ℝ) 1) ∧
       (∀ x ∈ S, (butcherShiftedLegendre n).eval x = 0)
   ```
   or the multiset/`Polynomial.roots` form, depending on Aristotle's
   formulation. Reformulate if Aristotle's exact statement diverges
   from the cycle 294 submission.
5. **Verify axiom-clean**: `#print axioms` on the headline must return
   `[propext, Classical.choice, Quot.sound]`. No new axioms.
6. **Retain the empirical anchors** (`n ∈ {1, 3, 5, 7, 9, 11}`). They
   provide concrete numerical witnesses and may simplify downstream
   computations even after the general theorem lands. Do NOT delete.
7. **`lean_status.json`**: bump `lem:342A` from `partial` to
   `formalized`. **All seven (342a)–(342g) properties now closed.**
8. **`plan.md`**: bump `lem:342A` row from `[~]` to `[x]`. Update the
   §342 cluster progress note.
9. **Task results §"Worked on"**: emphasise that this closes the entire
   §342 (Gaussian quadrature foundation) cluster except for `lem:342B`
   (Gaussian quadrature exactness degree) and `thm:342C` (order-condition
   equivalence), both of which depend on `lem:342A` and now become
   single-cycle viable targets.

### §A' — Aristotle COMPLETE_WITH_ERRORS

If Aristotle returned a proof but with compile errors:

1. **Download** and **inspect** the errors. Common patterns:
   - Namespace-resolution errors (cf. cycle 184): the cycle 294
     submission cited theorems by `M.theorem_name` style; Aristotle may
     have written them in the wrong namespace. Fix with explicit
     `LinearMultistepMethod.xxx` / `OpenMath.Chapter3.Section342.xxx`.
   - Missing imports.
   - Tactic / simp set drift since cycle 294 submission.
2. **Apply fixes locally**. Time-box to **30 minutes** of fixing. If
   errors are substantial (>5 distinct issues), fall through to Branch B.
3. If a clean fix lands, proceed with §A steps 3–9.

### §B — Aristotle IN_PROGRESS at ≥29% (Branch B, healthy or first stall)

Ship the `n = 13` empirical anchor `butcherShiftedLegendre_thirteen_roots`.
This is mechanical extension of cycle 299's recipe.

**Critical preflight steps**:

1. **Python `Fraction` pre-verification**. Compute `P_13^*(x)` at the
   chosen 14 bracket endpoints + `1/2` *before* writing Lean. The
   closed form `butcherShiftedLegendre_thirteen` does NOT exist yet
   (cycles 287/278/280 stopped at `_eleven`); you will need to add it
   first. Recommend the cycle 287 `_eleven` template.

2. **Bracket grid**: outer brackets of `P_13^*` are tighter than n=11
   (≈ 0.008 vs ≈ 0.02). **Denominator 100 will likely be required**
   for the outer brackets (`(0, 1/100)` and `(99/100, 1)`). Inner
   brackets can use denominator 20 or 50 per the n=11 pattern.

   Suggested grid (verify with Python before committing):
   `(0, 1/100)`, `(1/100, 1/20)`, `(1/20, 1/10)`, `(1/10, 1/5)`,
   `(1/5, 3/10)`, `(3/10, 2/5)`, `(2/5, 9/20)`, then `r₇ = 1/2`,
   then parity-symmetric right brackets `(11/20, 3/5)`, `(3/5, 7/10)`,
   `(7/10, 4/5)`, `(4/5, 9/10)`, `(9/10, 19/20)`, `(19/20, 99/100)`,
   `(99/100, 1)`.

3. **Mandatory `clear` step** (cycle 299 discovery): insert
   `clear hP13 hcont hf_0 hf_1 hf_<frac>...` (retaining only `hf_half`
   + IVT `hrᵢ_*` outputs) **immediately before the post-`refine` block**.
   Without this, `linarith` will time out on `isDefEq` preprocessing of
   the large-rational `hf_*` hypotheses. Outer-bracket denominators at
   n=13 will be on the order of 10^25+, making the timeout effectively
   guaranteed without the clear.

4. **Closed form first**: add `butcherShiftedLegendre_thirteen` to
   Section342.lean using the cycle 287 odd-`n` template:
   - `Nat.choose` decide-helpers at `k ∈ {2..13}`.
   - Per-`k` `simp` arms with `norm_num`.
   - Outer Butcher sign `(-1)^13 = -1` flips every coefficient and
     gives constant term `-1`.
   - Leading coefficient `Nat.choose 26 13 = 10400600`.

5. **Workflow**:
   1. Write the Python pre-verification snippet (record results in a
      comment block at the top of the new theorem for reference).
   2. Add `butcherShiftedLegendre_thirteen` closed form (~80 LOC).
   3. Add `butcherShiftedLegendre_thirteen_roots` (~450 LOC):
      - 14 `hf_*` bracket evaluations.
      - Middle via `butcherShiftedLegendre_eval_half_eq_zero_of_odd 13 ⟨6, rfl⟩`.
      - 12 IVT calls (alternating ascending/descending per parity).
      - **Insert `clear` block here.**
      - `refine` with 13 distinct roots + 78 distinctness pairs.
   4. Verify `lake env lean OpenMath/Chapter3/Section342.lean` exits 0.
   5. Axiom check.

6. **Stall observation**: if Aristotle returned exactly 29% (flat from
   cycle 299), record this as **stall observation #1**. Per cycle 285
   three-stall protocol, do NOT cancel yet — only observe.

### §C — Aristotle IN_PROGRESS at <29% (Branch C, regression)

Regression below 29% is **unexpected** but possible (e.g. if Aristotle
backtracked from a failed proof attempt). Action:

1. **Record the regression** in cycle 300 task results.
2. **Do NOT cancel yet**. Regression-then-recovery is a normal
   exploration pattern.
3. Proceed with **§B (n=13 anchor)** as the cycle deliverable.
4. If next cycle's poll shows another regression or no recovery, that
   becomes observation #1 of a new stall protocol.

### §D — Aristotle FAILED or cancelled

If Aristotle returned `FAILED` or has been cancelled:

1. **Investigate**: download the failure log if available.
2. **Pivot to manual closure**. Open a new issue file
   `.prover-state/issues/lem_342A_g_zeros_manual_closure_plan.md`
   modelled on `lem_342A_342f_manual_closure_plan.md` (cycle 289), with
   a phased manual approach:
   - Phase A: sign-change cardinality lemma (`P_n^*` has ≥ `n`
     sign-change zeros in `(0,1)` from any candidate set of bracket
     endpoints).
   - Phase B: product polynomial construction `Q := ∏ (X - xᵢ)` over
     the assumed sign-change set, with `Q.natDegree < n`.
   - Phase C: contradiction via cycle 292's
     `butcherShiftedLegendre_orthogonal_to_lower_degree`:
     `∫₀¹ P_n^* · Q = 0` while the integrand has constant sign on
     each sub-interval.
   - Phase D: capstone combining the cardinality lemma with the
     general-`n` distinctness conclusion.
3. Estimated 4–6 cycles total. Mirror the Phase A.1/A.2/A.3 cadence
   from `lem_342A_342f_manual_closure_plan.md`.
4. **Cycle 300 deliverable**: scoping doc + Phase A.1 starter lemma
   (sign-change → root cardinality). Single-cycle target ~80–120 LOC.

## What NOT to try

* **Do NOT re-poll Aristotle within this cycle.** One poll only per
  CLAUDE.md. If `IN_PROGRESS`, accept it and move on.
* **Do NOT cancel Aristotle prematurely** if stall counter is not at 3
  consecutive observations. Cycle 299 reset the counter; do not act on
  one new flat reading alone.
* **Do NOT extend the empirical ladder past `n = 13` in cycle 300.**
  The marginal value drops sharply after n=11. If Aristotle stalls
  hard, pivot to manual closure (§D) rather than continuing to n=15+.
* **Do NOT attempt the `n = 13` proof without the cycle 299 `clear`
  step.** The `linarith` / `isDefEq` timeout is *guaranteed* at this
  bracket-denominator scale. The `clear` is not optional infrastructure;
  it is required.
* **Do NOT use `Polynomial.ext` on `butcherShiftedLegendre_thirteen`**.
  Use the cycle 287 `_eleven` template (per-`k` simp arms + `norm_num`),
  which is the only tactic shape known to close `Polynomial ℝ`
  closed-form witnesses at this size without timing out.
* **Do NOT introduce `axiom` / `constant`** to bridge any (342g) gap.
  Manual closure (§D) is the fallback if Aristotle fails.
* **Do NOT pivot to a fresh entity in cycle 300** unless Aristotle
  returns `COMPLETE` and the §342 cluster fully closes. The §342 ladder
  has compounding value; finishing it cleanly takes priority over
  cluster-switching.
* **Do NOT raise `maxHeartbeats` above 200000.** If `n=13` stalls
  somewhere unexpected, decompose into named helper lemmas (cycle 281
  pattern).
* **Do NOT attempt to compile `OpenMath/Chapter4/Section441.lean`**.
  45+ consecutive GPFS timeouts since cycle 182 (per
  `cycle_182_gpfs_slowness.md`). Skip without smoke-testing.
* **Do NOT modify `scripts/autonomous_loop.py`** or the prompt-builder.
  Loop-maintainer territory.

## Faithfulness & housekeeping

* Cycle 300's deliverable updates `lean_status.json` only on Branch A
  (full closure). Branches B/C/D keep `lem:342A` as `partial` /
  `plan.md` row as `[~]`.
* Branch B's `_thirteen` and `_thirteen_roots` are not textbook
  entities — they are anchors of the unformalized general claim. Do
  NOT promote `plan.md` rows for them.
* Tautology-scanner regex must return 0 hits on Section342.lean before
  closing the cycle.

## Bottom line

1. Poll Aristotle once.
2. Branch on the result per the decision table.
3. Most likely path: **Branch B (n=13 anchor)** with cycle 299's `clear`
   step baked into the template.
4. Less likely but high-payoff: **Branch A (integrate general theorem)**
   if Aristotle finished. This would close `lem:342A` end-to-end.
5. Fallback: **Branch D (manual closure plan)** if Aristotle fails.
   Scoping + Phase A.1 starter as the cycle deliverable.
