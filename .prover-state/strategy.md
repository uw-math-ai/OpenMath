# Cycle 301 Strategy

## Context

Cycle 300 shipped the `n = 13` empirical anchor for `lem:342A` clause
(342g) and observed Aristotle project `5939f28b-c890-4b7f-be4f-ed0f31f0d0b5`
at **30 %** (+1 pp from cycle 299's 29 %, healthy growth). The cycle 300
planner **explicitly warned against extending the empirical ladder past
`n = 13`** in cycle 301. The empirical anchors `n ∈ {1, 3, 5, 7, 9, 11, 13}`
are now sufficient evidence; further `n = 15, 17, …` add marginal value.

`lem:342A` remains `[~]` partial: clauses (342a)–(342f) are all closed
axiom-clean (cycles 271–293, 277 for orthogonality, 293 for recurrence),
plus seven concrete-`n` empirical anchors for (342g). Only general (342g)
is open.

## §A — Priority 0 (MANDATORY, do this FIRST, ≤ 5 minutes)

**Single Aristotle poll** on project `5939f28b-c890-4b7f-be4f-ed0f31f0d0b5`
via `mcp__aristotle__get_status`. Record the percent and `status` in the
task results.

Per CLAUDE.md: **do NOT re-poll within the same cycle.** If the first
call fails (rate-limit, network), wait and retry once, then proceed with
the non-COMPLETE branch using the last-known 30 % observation from cycle 300.

## §B — Branch table (commit to ONE branch based on §A result)

| Aristotle status | Branch | Action |
|---|---|---|
| `COMPLETE` (100 %) | **A** | Integrate the general (342g) proof. Highest priority. |
| `COMPLETE_WITH_ERRORS` | **A′** | Integrate with surgical fixes (mirror cycle 277 / 281 / 184 integration patterns). |
| `IN_PROGRESS` ≥ 31 % | **B** | Healthy growth. Ship §C P1 (manual closure scoping + Phase A.1 stepping stone). |
| `IN_PROGRESS` = 30 % | **C** | **First stall observation** (cycle 300 saw 30 % growth from 29 %; flat 30 % is now obs #1 of cycle 285 three-stall protocol). Do NOT cancel. Ship §C P1. |
| `IN_PROGRESS` < 30 % | **D** | Regression. Note as obs #1 of stall protocol (regression treated same as flat). Do NOT cancel. Ship §C P1. |
| `FAILED` | **E** | Cancellation triggered. Ship §C P1 immediately (it is the manual closure plan that this branch needs). |

**Branches B, C, D, E all do the same work — §C P1 below.** The only
exception is Branch A / A′ (integration).

The cycle 285 three-stall protocol requires three consecutive flat-or-
regressed observations before cancellation. Cycle 301 can only ever be
obs #1 (since cycle 300 was the last healthy-growth observation); do
NOT cancel Aristotle this cycle regardless of which non-COMPLETE branch
fires.

## §C — Branch B/C/D/E deliverable (default work)

### P1 — Open manual closure scoping doc + ship Phase A.1 stepping stone

**File**: `.prover-state/issues/lem_342A_342g_manual_closure_plan.md`
(new file, ~250 LOC markdown). Model on the existing
`lem_342A_342f_manual_closure_plan.md` (cycle 289). Required sections:

1. **§1 Textbook statement** verbatim from
   `extraction/formalization_data/entities/lem_342A.json` clause (342g):
   "P_n^* has n distinct real zeros in the interval (0, 1), n = 0, 1, 2, …".
2. **§2 Textbook proof sketch**: sign-change contradiction.
   * Let the set of distinct sign-change zeros of `P_n^*` in `(0,1)` be
     `{x_1, …, x_k}` with `k < n` (toward contradiction).
   * Form `Q(x) := ∏ᵢ (x − xᵢ)` (degree `k`).
   * Then `P_n^*(x) · Q(x)` has constant sign on `(0, 1)` (sign-change
     zeros pair off between the two factors), so
     `∫₀¹ P_n^* · Q ≠ 0`.
   * But `deg Q = k < n`, so by cycle 292's
     `butcherShiftedLegendre_orthogonal_to_lower_degree`,
     `∫₀¹ P_n^* · Q = 0`. Contradiction.
   * Therefore `k ≥ n`. Combined with cycle 294's
     `butcherShiftedLegendre_card_roots_le` (`≤ n` upper bound), exactly
     `n` distinct sign-change roots in `(0,1)`.
3. **§3 Project-hook inventory** (already shipped, axiom-clean):
   * `butcherShiftedLegendre_orthogonal_to_lower_degree` (cycle 292,
     `Section342.lean:3032`) — the load-bearing input.
   * `butcherShiftedLegendre_orthogonal` (cycle 277).
   * `butcherShiftedLegendre_natDegree` (cycle 273).
   * `butcherShiftedLegendre_card_roots_le` (cycle 294) — upper bound.
   * `Polynomial.continuous` + `intermediate_value_Ioo`.
   * `Polynomial.roots`, `Polynomial.roots.toFinset`.
4. **§4 Mathlib-hook checks** (verify with `lean_local_search` /
   `lean_loogle` in cycle 302+ before consuming):
   * Sign-change extraction: likely needs a custom helper
     `Polynomial.signChangeRoots`; Mathlib does not appear to have a
     direct "set of sign-change zeros" predicate.
   * Constant sign on Ioo: continuity + `intermediate_value_Ioo`
     pairwise argument.
   * Polynomial product non-vanishing: `Polynomial.prod_X_sub_C`,
     `Polynomial.eval_prod`.
5. **§5 Phase decomposition** (4 phases, 3–4 cycle estimate):
   * **Phase A.1 (this cycle, P1.b below)**: `signChangeRoots`
     definition + cardinality-upper-bound lemma.
   * **Phase A.2 (cycle 302)**: Sign-constancy of `P_n^*(x) · Q(x)`
     on `(0,1)` when `Q` collects all sign-change roots.
   * **Phase A.3 (cycle 303)**: Integral nonvanishing via positivity
     on the sign-constant product.
   * **Phase A.4 (cycle 304)**: Contradiction closure via (342a)
     orthogonality. Ship `butcherShiftedLegendre_distinct_roots`.
6. **§6 Risk assessment**: LOC estimates per phase, Aristotle
   suitability ratings, alternative bypass routes (e.g. Sturm-sequence
   argument as fallback if sign-change combinatorics stalls).
7. **§7 Cycle 302 entry point**: Phase A.2 deliverable spec.

**P1.b (Phase A.1 stepping stone)**: ship a single reusable lemma in
`OpenMath/Chapter3/Section342.lean` (NOT in a new file — keep §342
cohesive). Append immediately after
`butcherShiftedLegendre_card_roots_le` (cycle 294 location).

```lean
/-- The Finset of distinct real roots of `p` in the open interval `(a, b)`.
This is a subset of `p.roots.toFinset` whose cardinality is bounded by
`p.natDegree`. -/
noncomputable def Polynomial.rootsIn (p : Polynomial ℝ) (a b : ℝ) :
    Finset ℝ :=
  p.roots.toFinset.filter (fun x => x ∈ Set.Ioo a b)

/-- The number of distinct real roots of `p` in `(a, b)` is bounded
above by the natural degree of `p`. -/
theorem Polynomial.rootsIn_card_le (p : Polynomial ℝ) (a b : ℝ) :
    (p.rootsIn a b).card ≤ p.natDegree := by
  unfold Polynomial.rootsIn
  exact le_trans (Finset.card_filter_le _ _)
    (le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' p))
```

Two non-vacuity `example`s on `butcherShiftedLegendre {1, 3}`
confirming `(P_n^*.rootsIn 0 1).card ≤ n`, leveraging the cycle
295/297 anchors. Both should close by `simpa using
Polynomial.rootsIn_card_le _ _ _` after substituting
`butcherShiftedLegendre_natDegree`.

**Note**: this is the *cardinality-upper-bound* piece. The
*sign-change* refinement (distinguishing sign-changes from tangencies)
is Phase A.2 work — the contradiction argument only needs sign-change
roots, but for `P_n^*` every real root in `(0,1)` is automatically a
sign change because `P_n^*` is squarefree (its derivative `n·P_n^*`
has no common zero with `P_n^*` on `(0,1)` since the recurrence (342f)
combined with linear independence forces simple roots). Document this
in §5 of the scoping doc.

**Why this work is always useful**:
- If Aristotle returns COMPLETE in cycle 302, the scoping doc + Phase A.1
  ship is ~50 LOC of clean reusable polynomial machinery, possibly
  already needed by Aristotle's proof.
- If Aristotle stalls / fails, cycle 302's planner has a concrete 3-phase
  plan to execute.

LOC budget: **~150 LOC total** (scoping doc ~250 lines markdown ≈ 0 LOC
of Lean; Phase A.1 is ~30–50 LOC of Lean + 10 LOC of `example`s).
Aristotle suitability for P1.b: high (mechanical Finset cardinality).

## §D — Branch A / A′ deliverable (Aristotle COMPLETE)

### P1 — Integrate Aristotle's general (342g) proof

1. **Download** the result: `mcp__aristotle__download_result` for project
   `5939f28b-c890-4b7f-be4f-ed0f31f0d0b5`. Extract the proof file to
   `.prover-state/aristotle_results/cycle_301/`.

2. **Read `ARISTOTLE_SUMMARY.md`** if present. Note the proof strategy
   (sign-change / Sturm / IVT cardinality) and any helper lemmas
   Aristotle introduced.

3. **Mirror cycle 281 integration pattern**: extract any new
   reusable polynomial / sign / integral helpers to a new file
   `OpenMath/Chapter3/Section342DistinctRootsHelpers.lean` (mirror
   `Section342NormSqHelpers.lean`). Keep main `Section342.lean`
   clean — only the public theorem `butcherShiftedLegendre_distinct_roots`
   lives there.

4. **Headline theorem** target signature:

   ```lean
   theorem butcherShiftedLegendre_distinct_roots (n : ℕ) :
       ∃ rs : Fin n → ℝ,
         Function.Injective rs ∧
         (∀ i, rs i ∈ Set.Ioo (0 : ℝ) 1) ∧
         (∀ i, (butcherShiftedLegendre n).eval (rs i) = 0)
   ```

   (Match Aristotle's exact signature if it differs — but verify the
   conclusion captures "n distinct real zeros in (0, 1)" per the
   textbook entity JSON.)

5. **Verify**:
   * `lake env lean OpenMath/Chapter3/Section342.lean` exit 0.
   * `lake env lean OpenMath/Chapter3.lean` exit 0 (aggregator).
   * `lean_verify` axiom-clean on the new theorem
     (`[propext, Classical.choice, Quot.sound]`).
   * Sorry count remains 0.

6. **Cross-check against empirical anchors** (cycles 295–300):
   each `butcherShiftedLegendre_{one,three,five,seven,nine,eleven,
   thirteen}_roots` should be derivable as a corollary of the general
   theorem specialized at the corresponding `n`. **Do NOT delete the
   empirical anchors** — they serve as defensive regression tests and
   provide explicit closed-form root witnesses (which the existential
   general theorem does not). Add a `/-- Cross-check: the cycle 300
   `_thirteen_roots` empirical anchor is consistent with the general
   theorem. -/` comment near the headline.

7. **Update bookkeeping** (Branch A only):
   * `extraction/formalization_data/lean_status.json`: `lem:342A`
     `partial` → `formalized`, `lean_symbol` updated to include
     `butcherShiftedLegendre_distinct_roots`, `last_modified` to cycle 301.
   * `plan.md`: `[~] lem:342A` → `[x] lem:342A` with note "all 7
     clauses (342a)–(342g) closed cycle 271–301".
   * `.prover-state/issues/lem_342A_g_zeros_scoping.md`: append "Cycle 301
     closure" section marking the scoping doc resolved.

8. **Faithfulness audit**: per CLAUDE.md pre-commit checklist, confirm
   * No new `axiom` / `constant` declarations.
   * No `sorry` in the integrated proof.
   * The Lean conclusion matches the textbook clause (342g) word-for-word
     in essence ("`P_n^*` has `n` distinct real zeros in `(0, 1)`").
   * No hypotheses stronger than `n : ℕ` (the textbook statement is
     unconditional in `n`, including `n = 0` where the empty `Fin 0 → ℝ`
     trivially witnesses).

## §E — What NOT to do

* **Do NOT extend the empirical ladder to `n = 15`**. Planner
  explicitly warned in cycle 300 against this. Marginal value of an
  eighth concrete anchor is low; defer indefinitely unless Aristotle is
  cancelled in cycle 302+ and the manual closure stalls.

* **Do NOT re-poll Aristotle within cycle 301**. CLAUDE.md single-poll
  rule. Even if the first poll shows IN_PROGRESS at 30 %, do NOT poll
  again later in the cycle hoping for COMPLETE.

* **Do NOT cancel Aristotle this cycle.** Cycle 285 three-stall protocol
  requires three consecutive flat / regressed observations. Cycle 301
  is at most obs #1.

* **Do NOT touch `OpenMath/Chapter4/Section441.lean`**. GPFS pathology
  is 43+ timeouts since cycle 182; skip per
  `.prover-state/issues/cycle_182_gpfs_slowness.md`. Section381 / 342 /
  300 / 310 / 311 compile healthy and remain the cycle's scope.

* **Do NOT introduce sorry-first scaffolds for `lem:342B`,
  `thm:342C`, or `cor:342D`**. Each is blocked on either (342g)
  (`lem:342B` direct) or on simplifying-assumption infrastructure
  (`thm:342C`); attempting any of them this cycle violates the
  cycle 200 / 201 / 138 / 139 / 149 / 150 sorry-rollback precedent.

* **Do NOT pivot to a fresh §381 / §310 entity unless Aristotle
  returns FAILED.** The §342 closure path has clear momentum and the
  manual closure scoping doc unblocks 3 cycles of substantive work.

* **Do NOT raise `maxHeartbeats` above 200000.** If sign-change
  combinatorics stall on simp, decompose into named intermediate
  lemmas (cycle 280's `matrix7_oneMinusZSmul_det` precedent).

* **Do NOT modify `scripts/autonomous_loop.py` or the prompt-builder**.
  Tautology-scanner / empty-stuck-on phantoms are loop-maintainer
  territory per `.prover-state/issues/tautology_scanner_false_positives.md`.

* **Do NOT submit a new Aristotle job for (342g) in cycle 301**. One
  is already in flight; firing a second wastes the slot. If `5939f28b`
  must be cancelled in cycle 302+, the resubmission strategy goes in
  the new scoping doc, not this strategy.

## §F — Risk register (cycle 301-specific)

| Risk | Likelihood | Mitigation |
|---|---|---|
| Aristotle returns COMPLETE with proof relying on a Mathlib gap | low | Integration step §D.3 isolates helpers in a dedicated file; if a gap appears (e.g. `Polynomial.sign_variations` not in Mathlib), close it with a hand-written lemma in the helper file |
| `rootsIn_card_le` (P1.b) fails because `Polynomial.card_roots'` signature drifted | low | Cycle 294 already uses `Polynomial.card_roots'` successfully in `butcherShiftedLegendre_card_roots_le`; reuse that exact pattern |
| `Multiset.toFinset_card_le` returns the wrong shape | low | Inline-test with `lean_multi_attempt` if first compile fails |
| `Polynomial.rootsIn` namespace collision (Mathlib may already export this name) | medium | Verify with `lean_local_search "Polynomial.rootsIn"` before introducing; if collision, use `butcherShiftedLegendre.rootsIn` or `Section342.rootsIn` |
| Aristotle COMPLETE but proof uses `≥ 200000` heartbeats | low | Surgical decomposition mirroring cycle 281's `Section342NormSqHelpers.lean` extraction |
| Scoping doc Phase A.1 lemma trivially follows from `card_roots_le` (cycle 294) | medium | Acceptable — the value is the scoping doc and Phase A.2/A.3 setup, not the trivial Phase A.1 |
| Phase A.1 ships axiom-clean but adds a tautology-scanner false positive | low | Rename any `h_<name>` → `h<name>` proactively per cycle 154 precedent |

## §G — Deliverable bar for cycle 301

**Minimum acceptable** (per CLAUDE.md "zero-change cycle is unacceptable"):
* Aristotle poll executed and observation recorded.
* Either **integration of (342g) general proof** (Branch A/A′) OR
  **scoping doc + Phase A.1 stepping stone** (Branches B/C/D/E).
* Axiom-clean (`[propext, Classical.choice, Quot.sound]` only); sorry
  count remains 0.
* Task results `.prover-state/task_results/cycle_301.md` documents the
  Aristotle observation, the branch taken, and the deliverable's
  faithfulness audit.

**Stretch (Branch A only)**:
* Update `lean_status.json` `lem:342A` → `formalized`.
* Cross-check all seven cycle 295–300 anchors derive from the general
  theorem (state as a comment block, not new theorems).

**Stretch (Branches B/C/D/E)**:
* Phase A.1 stepping stone ships with two non-vacuity `example`s
  (n = 1, n = 3).
* Scoping doc has all 7 sections (§1–§7) populated with at least one
  paragraph each.

## §H — Cycle 302 outlook (advisory only)

Depending on cycle 301's Aristotle observation:
* **If COMPLETE in cycle 301**: cycle 302 planner picks a fresh entity
  pivot. Natural candidates: `lem:342B` (Gaussian quadrature exactness;
  now unblocked since (342g) provides the zeros) or pivot back to
  `lem:310B` Phase A.3 (TreeAutomorphism strengthening).
* **If still IN_PROGRESS in cycle 302**: cycle 302 ships Phase A.2 of
  the manual closure plan (sign-constancy of `P_n^* · Q` on `(0, 1)`).
  Aristotle observation #2 of 3.
* **If FAILED or cancelled in cycle 302**: cycle 302 ships Phase A.2,
  plus optionally a defensive resubmission strategy in the scoping doc.

---

Cycle 300 closed a complete and verified empirical ladder. Cycle 301
executes one Aristotle poll, branches cleanly, and ships substantive
work regardless of outcome. No cherry-picking, no scope creep.
