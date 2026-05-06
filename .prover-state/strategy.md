# Cycle 160 Strategy

## Status snapshot

* **Sorry count: 0** — clean.
* **Cycle 159 just landed** (axiom-clean): r = 3 non-vacuity witnesses
  for `def:530B`/`def:530C` Path A. The four-corner grid r ∈ {1, 2, 3}
  × p ∈ {0, 1} is now saturated.
* `def:530B`/`def:530C` remain `[~]` partial: Path B (implicit, via
  `ContractingWith` / `Function.IsFixedPt`) is multi-cycle
  infrastructure and intentionally deferred per
  `.prover-state/issues/def_530B_scaffold_strategy.md`.
* No pending Aristotle results.
* No active blockers escalated by the previous cycle.

## What I considered

Per the planner rule "no sorries, no in-progress theorems → pick the
next theorem from plan.md", I surveyed candidate pivots. The cycle
159 worker's suggested-next-approach list was the starting point.

| Candidate | Verdict |
|---|---|
| `def:451A` (G-stable, Ch4 §451) | Requires "one-leg method" infrastructure + matrix M from eq (451e) — both absent from codebase. Multi-cycle. |
| `def:422B` (LMM underlying one-step method, Ch4 §422) | Requires Butcher-group `G_1` (mappings RootedTree → ℝ) + tree operator D + Φ mapping. Touches §381/§383 group infrastructure. Multi-cycle. |
| `thm:381G` (Ch3 §380) | Requires elementary-weight infrastructure + algebraic-partition argument over `Fin s` stages. lem:312B / lem:310B (deps) are open. Multi-cycle. |
| `thm:521B` (Ch5 §521) | Requires complex partial-fraction expansion + contour integration + Padé exponential infrastructure. Multi-cycle. |
| Path A r = 4 lift (cycle 159 worker's #2) | Mechanical port of cycle 159, but worker explicitly noted "substantive interest peters out beyond r = 3" without an r-parametric refactor. Diminishing returns. Held in reserve as Backup A. |
| **Taylor-degree parametric helper refactor** (cycle 159 worker's #1) | Cycle 159 worker's explicit cycle-160 recommendation. Mechanical, low-risk, compounds cycle 158 abstraction. **Selected.** |

## Cycle 160 target — extract the p = 0 sibling helper

**Goal**: lift the cycle 153 inline T1 + T2 closure body into a free-
standing private helper analogous to cycle 158's
`taylor_lipschitz_explicitEuler_orderOne_diff_isBigO`, then refactor
the three p = 0 witness call sites (cycles 153, 156, 159) to invoke
it as a one-liner. Net LOC delta expected: ≈ −290.

**Current call-site grid** (5 substantive sites + cycle 158 helper):

| Cycle | Theorem (i = 0 channel only for r ≥ 2) | p | r | Uses cycle 158 helper? |
|---|---|---|---|---|
| 153 | `explicitEulerGLM_hasOrderZero_trivialStarting` | 0 | 1 | NO — direct T1+T2 inline (~180 LOC) |
| 154 | `explicitEulerGLM_hasOrderOne_trivialStarting` | 1 | 1 | YES — one-line via cycle 158 helper |
| 156 | `padded2DEulerGLM_hasOrderZero_padCompatStarting` | 0 | 2 | NO — direct T1+T2 inline |
| 157 | `padded2DEulerGLM_hasOrderOne_padCompatStarting` | 1 | 2 | YES |
| 159 | `padded3DEulerGLM_hasOrderZero_pad3CompatStarting` | 0 | 3 | NO — direct T1+T2 inline |
| 159 | `padded3DEulerGLM_hasOrderOne_pad3CompatStarting` | 1 | 3 | YES |

The p = 0 sites duplicate the cycle 153 closure: T1 little-o(h) via
`hasDerivAt_iff_isLittleO_nhds_zero`; T2 O(h) via Lipschitz +
continuity-driven eventual `|·| ≤ 1`. Refactoring them to share a
helper mirrors cycle 158's p = 1 refactor.

## Concrete steps

### Step 1 — Read context (5 min)

Use `lean_hover_info` / `lean_file_outline` on
`OpenMath/Chapter5/Section530.lean` to confirm the current line
numbers of:
* the cycle 158 helper
  `taylor_lipschitz_explicitEuler_orderOne_diff_isBigO`,
* the cycle 153 witness body of
  `explicitEulerGLM_hasOrderZero_trivialStarting`,
* the cycle 156 i = 0 channel of
  `padded2DEulerGLM_hasOrderZero_padCompatStarting`,
* the cycle 159 i = 0 channel of
  `padded3DEulerGLM_hasOrderZero_pad3CompatStarting`.

Do NOT read the whole file with `Read` — it is ~2030 LOC. Use
`lean_file_outline` for skeleton, then targeted `Read` with `offset`
+ `limit` for the four sites above.

### Step 2 — Design the new helper signature

Place the new helper **immediately before** the cycle 158 helper.
File order after the cycle: orderZero helper → orderOne helper
(cycle 158) → cycle 153/154/156/157/159 witnesses.

```lean
private theorem taylor_lipschitz_explicitEuler_orderZero_diff_isBigO
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv_x₀ : HasDerivAt yex (f y₀) x₀) :
    (fun h : ℝ => ((y₀ + h * f y₀) + h * f (y₀ + h * f y₀))
                  − (yex (x₀ + h) + h * f (yex (x₀ + h))))
      =O[nhds (0 : ℝ)] (fun h => h ^ (0 + 1)) := by
  -- Lift the cycle 153 inline body verbatim:
  --   T1 := (y₀ + h·f y₀) − yex(x₀+h)  is little-o(h) via
  --     `hasDerivAt_iff_isLittleO_nhds_zero.mp hyex_deriv_x₀`,
  --     after rewriting via `hyex_x₀` and `smul_eq_mul`,
  --     then `IsLittleO.neg_left` and `IsLittleO.isBigO`.
  --   T2 := h · (f(y₀ + h·f y₀) − f(yex(x₀+h)))  is O(h) via
  --     Lipschitz `dist_le_mul`, with the `|a − b| ≤ 1` clause
  --     supplied by continuity at 0 of `a := y₀ + h·f y₀` and
  --     `b := yex(x₀+h)` plus `Metric.tendsto_nhds.mp +
  --     Real.dist_0_eq_abs`.
  --   Combine via `hT1.add hT2`; `simp` collapses `h ^ (0 + 1)` → `h`.
  sorry
```

(Don't actually leave the `sorry`; this is just the prose target.
Lift the cycle 153 body intact.)

### Step 3 — Lift the cycle 153 body into the helper

The cycle 153 witness `explicitEulerGLM_hasOrderZero_trivialStarting`
contains the canonical T1 + T2 closure. Open the witness, **isolate
the post-rewrite tail** that produces the `=O[nhds 0] (fun h => h)`
conclusion on the diff
```
((y₀ + h * f y₀) + h * f (y₀ + h * f y₀))
  − (yex (x₀ + h) + h * f (yex (x₀ + h)))
```
and copy it verbatim into the new helper's body. Adjust hypothesis
names if needed to match the helper's signature.

The witness's pre-rewrite preamble (the `intro`s, the `change` to
the explicit `padded`-or-trivial GLM closed form, the `simp` reducing
SM / ES applications) stays at the witness call site; only the tail
lifts.

### Step 4 — Refactor the three p = 0 call sites

For each of the three witnesses (cycle 153, cycle 156's i = 0
channel, cycle 159's i = 0 channel), replace the inline T1 + T2 tail
with a single `exact` invoking the new helper. Mirrors the cycle 154
/ 157 / 159 i = 0 channel pattern (which uses the cycle 158 p = 1
helper as a one-liner after the SM[0] / ES[0] closed-form rewrites
plus an `h ^ (1 + 1) = h ^ 2` collapse).

For p = 0, the collapse is `h ^ (0 + 1) = h`, also one `simp` /
`ring` step.

**Cycle 153 site**:
```lean
-- After the existing closed-form rewrites...
-- replace the long T1+T2 inline body with:
exact taylor_lipschitz_explicitEuler_orderZero_diff_isBigO
        hf_lip hyex_x₀ hyex_deriv_x₀
```

**Cycle 156 i = 0 site** and **cycle 159 i = 0 site**: same pattern.
The i ≥ 1 zero-collapse channels are untouched.

### Step 5 — Verify no regression (mandatory)

1. `lake env lean OpenMath/Chapter5/Section530.lean` exits 0.
2. `lake env lean OpenMath/Chapter5.lean` exits 0 (full module).
3. `grep -c sorry OpenMath/Chapter5/Section530.lean` → 0.
4. Tautology-scanner regex clean (use the Grep tool, not raw rg):
   pattern `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` on
   `OpenMath/Chapter5/Section530.lean` → zero hits.
5. `lean_verify` axiom-clean
   (`[propext, Classical.choice, Quot.sound]`) on:
   * the new
     `taylor_lipschitz_explicitEuler_orderZero_diff_isBigO` helper,
   * `explicitEulerGLM_hasOrderZero_trivialStarting`,
   * `padded2DEulerGLM_hasOrderZero_padCompatStarting`,
   * `padded3DEulerGLM_hasOrderZero_pad3CompatStarting`,
   * the three `def:530C` consumer wrappers
     `explicitEulerGLM_hasOrderZero`,
     `padded2DEulerGLM_hasOrderZero`,
     `padded3DEulerGLM_hasOrderZero`.
6. `lean_verify` axiom-clean re-check on the cycle 158 helper and
   its three p = 1 consumers (UNTOUCHED but the refactor's main
   failure mode is inadvertent breakage upstream — verify
   explicitly):
   * `taylor_lipschitz_explicitEuler_orderOne_diff_isBigO`,
   * `explicitEulerGLM_hasOrderOne_trivialStarting`,
   * `padded2DEulerGLM_hasOrderOne_padCompatStarting`,
   * `padded3DEulerGLM_hasOrderOne_pad3CompatStarting`,
   * the three `def:530C` p = 1 wrappers.
7. **Net LOC**: expect ~−290 LOC (each of three sites shrinks by
   ~130 LOC; new helper adds ~110 LOC).

### Step 6 — Bookkeeping

* **`plan.md`** — extend the rows for `def:530B` and `def:530C`
  with a cycle 160 note in the same style as cycles 156–159:
  "Cycle 160: shared T1+T2 helper extracted at the p = 0 sites
  (analog of cycle 158's p = 1 refactor); both p = 0 and p = 1
  closures now bottle-neck through one parametric pair of helpers,
  saving ~290 LOC across cycles 153/156/159. Path B (implicit
  branch) remains deferred."
* **`.prover-state/issues/def_530B_scaffold_strategy.md`** — append a
  "Cycle 160 update — shared T1+T2 helper landed" section recording
  the new helper, the three refactored call sites, the LOC delta,
  the axiom-clean status, and that cycles 158 / 160 together form
  a complete shared-machinery cover for the explicit-Euler i = 0
  channel at p ∈ {0, 1}.
* **`extraction/formalization_data/lean_status.json`** — bump cycle
  reference for `def:530B` and `def:530C` from 159 → 160. No status
  change; both stay `partial` since Path B is still deferred.

### Step 7 — Task results

Write `.prover-state/task_results/cycle_160.md` per CLAUDE.md format.

**Faithfulness check**: trivial. No new mathematical content, no
new entities, no statement changes, no hypothesis strengthening, no
theorem reformulation. The refactor packages cycles 153/156/159's
existing closures into a named lemma. Document this explicitly so
the supervisor's faithfulness scanner doesn't flag the missing
"new def" or "new theorem" signals as anomalous.

## What NOT to do

* **Do NOT lift to r = 4 as the primary path.** Cycle 159 worker
  explicitly noted "substantive interest peters out beyond r = 3"
  without an r-parametric refactor. Held as Backup A.
* **Do NOT define an `r`-parametric padded GLM family
  `paddedRDEulerGLM (r : ℕ)`.** Multi-cycle refactor; out of scope.
* **Do NOT pivot to def:451A, def:422B, thm:381G, thm:521B,
  thm:535A, or any other open Chapter 4/5 entity this cycle.** Each
  one requires multi-cycle infrastructure (one-leg methods, Butcher
  tree group `G_1`, elementary-weight algebra over `Fin s`,
  Padé / contour-integration machinery). These are valid future
  targets after dedicated infrastructure cycles.
* **Do NOT attempt `def:530B`/`def:530C` Path B (implicit-method
  fixed-point closure).** Multi-cycle per the deferred issue file.
* **Do NOT introduce a sum-typed regularity flag
  `ExplicitEulerOrderHyps` to make a SINGLE helper covering both
  p = 0 and p = 1.** Encoding A in earlier drafts of this strategy
  proposed this; rejected because the inductive-type overhead adds
  more boilerplate than the two-helper shape it would replace, and
  the consumer call sites still need a per-p discharge anyway.
  Stick with two siblings (cycle 158 = orderOne, new = orderZero).
* **Do NOT raise `maxHeartbeats` above 200000.** If the helper body
  is slow, decompose into named sub-lemmas (cycle 150 / 158
  precedent: split matrix-expansion `simp` from the closure
  `ring` / `IsBigO.add` step).
* **Do NOT introduce `axiom` or `constant` declarations.**
* **Do NOT skip the post-refactor `lean_verify` re-check on the
  p = 1 cycle 158 helper and its consumers (Step 5.6).** The
  refactor's main failure mode is inadvertent upstream breakage
  (e.g. simp set pollution, namespace shadowing); the verify step
  catches this.
* **Do NOT use names like `h_inner`, `h_deriv`, `h_yex` etc. with
  underscores.** Per
  `.prover-state/issues/tautology_scanner_false_positives.md`, the
  supervisor's scanner over-fires on `:= h_<name>` /
  `exact h_<name>`. Use `hyex_x₀`, `hderiv`, `hp` (no underscore
  separator after `h`) — the cycle 154 rename precedent.
* **Do NOT poll Aristotle this cycle.** No active submissions; no
  reason to fire one for a mechanical refactor. The cycle 148
  `thm:550A` general-`n` job at project `2c4630b2-…` was cancelled
  in cycle 151; do not re-poll.

## Backup plans

### Backup A — if Step 3 (p = 0 helper extraction) stalls past 90 minutes

**Symptom**: the cycle 153 inline T1 + T2 body uses ambient
bindings (e.g. specific shapes of `intro`, `change`, `fin_cases`)
that don't translate cleanly to a free-standing helper without
restructuring the surrounding proof scaffolding.

**Action**: skip the helper extraction. Pivot to the **r = 4
lift** (cycle 159 worker's suggestion 2):

* `OpenMath/Chapter5/Section520.lean`: add `padded4DEulerGLM :
  GeneralLinearMethod 1 4` with the same shape pattern as
  `padded2DEulerGLM` / `padded3DEulerGLM` (`A = !![0]`, row-0 active,
  rows 1-3 zero).
* `OpenMath/Chapter5/Section530.lean`: add `pad4CompatMethod`,
  `pad4CompatStartingMethod`,
  `pad4CompatStartingMethod_isNonDegenerate`,
  `pad4CompatStartingMethod_constituents_isExplicit`,
  `padded4DEulerGLM_isExplicit`,
  `pad4CompatStartingMethod_applyExplicit` (verbatim port of
  cycle 159's r = 3 infrastructure with one extra zero channel).
* Add `padded4DEulerGLM_hasOrderZero_pad4CompatStarting` (4-arm
  `fin_cases i`; i = 0 is cycle 156's T1 + T2 closure inlined; i = 1, 2,
  3 zero-collapse via `Asymptotics.isBigO_zero`).
* Add `padded4DEulerGLM_hasOrderOne_pad4CompatStarting` (4-arm; i = 0
  is cycle 158 helper one-liner; i = 1, 2, 3 zero-collapse).
* Add `def:530C` wrappers `padded4DEulerGLM_hasOrderZero` /
  `padded4DEulerGLM_hasOrderOne`.
* Remember to add `Fin.sum_univ_four` to the simp set in the SM[i]
  closed-form rewrites (cycle 159 hit this with `Fin.sum_univ_three`;
  cycle 144 hit it with `Fin.sum_univ_three`; the same auto-tag-
  status pattern applies — `Fin.sum_univ_four` is not default-tagged
  `@[simp]`).

Expected LOC delta: +500-600 (cycle 159 produced +523). All eight new
theorems should be axiom-clean by mechanical port. Score expectation: 2.

### Backup B — if BOTH primary refactor AND r = 4 lift stall

**Symptom**: cumulative time spent past 3 hours on this cycle without
a deliverable.

**Action**: deliver a minimal cycle to satisfy CLAUDE.md's "no zero
changes" rule:

1. Extract the post-rewrite simp set used for the SM[0] closed-form
   expansion at r ∈ {1, 2, 3} (the
   `simp [Matrix.mulVec, dotProduct, Fin.sum_univ_one,
   Fin.sum_univ_two, Fin.sum_univ_three, …]` boilerplate cycle 159
   discovered) into a `private lemma`. ~20 LOC.
2. Document the refactor stall in
   `.prover-state/task_results/cycle_160.md` with a precise blocker
   analysis (e.g. "the cycle 153 body destructures hypothesis
   `hyz : ⟨..⟩ = ⟨..⟩` whose binding shape doesn't lift to a
   free-standing helper without restructuring").
3. Add a fresh issue file
   `.prover-state/issues/cycle_160_helper_extraction_blocker.md`
   so cycle 161 can act on it.
4. Commit the small simp-set extraction + the issue file.

This guarantees a non-zero cycle even on full-stall.

## Single-cycle deliverable bar

* **Primary path**: 1 new private helper
  (`taylor_lipschitz_explicitEuler_orderZero_diff_isBigO`); 3
  refactored witness call sites (cycles 153/156/159); 3 unchanged
  consumer wrappers (`def:530C` shape) re-verified axiom-clean; 0
  new sorries; ~−290 LOC; bookkeeping in `plan.md`,
  `def_530B_scaffold_strategy.md`, `lean_status.json`.
  **Score expectation: 1-2** (refactor with multi-site validation;
  cycle 158 precedent scored 1, but multi-site coverage is
  comparable to a small substantive cycle).
* **Backup A path**: 8 new axiom-clean theorems at r = 4 plus 3 new
  defs and supporting infrastructure; +500-600 LOC; 0 new sorries.
  **Score expectation: 2** (matches cycles 156/157/159 shape).
* **Backup B path**: 1 small private simp-set helper + 1 documented
  blocker issue; +30 LOC. **Score expectation: 0-1** (safety net
  only).

## Why primary is preferred

The primary path's compound payoff is structural: cycle 158 + cycle
160 together form a complete shared-machinery cover for the
explicit-Euler i = 0 channel at p ∈ {0, 1}. After this cycle, future
r-extension or eventual `r`-parametric padded GLM family work becomes
strictly mechanical (one-line per channel rather than ~100 LOC per
channel). The r = 4 lift, if pursued in cycle 161, would benefit
directly from this cycle's helper extraction and shrink to ~half the
LOC of cycle 159's r = 3 lift.
