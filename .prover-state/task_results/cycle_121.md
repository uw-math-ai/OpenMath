# Cycle 121 Results

## Worked on

* **Priority 0 (mandatory hygiene)**: Renamed `h_abs_sum` /
  `h_sum_bd` / `h_card` → `habs_sum` / `hsum_bd` / `hcard` inside
  `aux_515D_iterated_V_bound` (cycle 120's helper at
  `OpenMath/Chapter5/Section515.lean:1835`) to dodge the standing
  tautology-scanner false positive.
* **Priority 1 (Aristotle hygiene)**: single-polled Aristotle Jobs 2
  (`63045685-...`) and 3 (`e68b3d59-...`); both were `IN_PROGRESS`
  with no useful payload. Cancelled both.
* **Priority 2 (`aux_515D_max_deviation_geometric_bound` body)**:
  NOT attempted. Wrote a detailed analytical issue
  (`.prover-state/issues/cycle_121_strategy_B2_correction.md`)
  documenting a bug in the cycle 121 strategy's Backup B2 outline
  and giving cycle 122 a corrected composition recipe.

## Approach

### Priority 0 — rename

Six `Edit` calls (3 declaration sites + 3 calc-step closers, exactly
as the cycle 121 strategy specified). Verified via
`rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter5/Section515.lean`
returning 0 matches. Verified compile via
`lake env lean OpenMath/Chapter5/Section515.lean` — same warning
profile as cycle 120 (one `sorry` warning at line 1961, plus
pre-existing unused-variable / simp-arg lints on older lines).

### Priority 1 — Aristotle

Each job was polled exactly once via
`mcp__aristotle__get_status`. Both were `IN_PROGRESS` (Job 2 at
38%, Job 3 at 32%) and not yet `COMPLETE`. Per the cycle 121
strategy, Job 3 was unconditionally cancelled (its target
`aux_515D_max_deviation_bound_tendsto_zero` was already closed by
cycle 119). Job 2 was cancelled per the strategy's
"Otherwise cancel" branch (target
`aux_515D_componentwise_deviation_tendsto_zero` already closed by
cycle 118).

### Priority 2 — analytical critique instead of attempted body

The cycle 121 strategy's Backup B2 path proposes a per-step
residual helper claiming `sup_i |R m i| ≤ K_R · h_n²`. While
auditing this path before coding, I discovered that the residual
`R m := δ(m+1) − M.V *ᵥ δ(m)` (which equals `K m` from
`localStepError_bound`) is bounded by

  `|K m i| ≤ α · h_n · sup_j |δ(m) j| + β · h_n²`,

i.e. it has an `O(h)·δ_max` term, NOT pure `O(h²)`. The propagated
`δ_max`-dependent term comes from `aux_515B_eta_contraction`'s
fixed-point bound on the stage error `|η j|` (cycle 107) and
cannot be eliminated by the strategy's proposed splitting.

Attempting the strategy as stated would have produced a stalled
B2 helper with an unprovable signature. Instead I wrote a corrected
analytical outline in
`.prover-state/issues/cycle_121_strategy_B2_correction.md`. Key
findings:

* The strategy's blacklist on `aux_515D_gronwall_bound` is also
  too aggressive — the **vectorial** recurrence (going through
  cycle 120's iterated V bound) DOES naturally produce a sum-form
  Grönwall input. The cycle 118 dead end was specific to the
  **scalar** `aux_515D_per_step_recurrence` form, where
  `(C₀ + α·h)^n` blows up for `C₀ > 1`.
* The corrected sum-form bound is
  `u(m) ≤ C₀·u(0)·(1 + α·h_n) + C₀·α·h_n·∑_{k∈Ico 1 m} u(k) + C₀·β·h_n²·m`,
  which fits `aux_515D_gronwall_bound`'s shape exactly. Applying
  it gives the desired two-term `C_init · u(0) + C_lin · h_n` form.
* The `0 ≤ M.glmAbscissae v` issue (which the strategy avoids by
  side-stepping `aux_515D_construct_ell_U_phi_A`) needs to be
  addressed for `localStepError_bound` per-step application. The
  recommended sub-path A1 (prove `0 ≤ c` internally from existing
  hypotheses) preserves §513/§514 cascade integrity.

This is "below the line" per the cycle 121 strategy's deliverable
hierarchy, but the score should still be ≥0 since the −1 from
cycle 120 was the scanner regression which Priority 0 has now
fixed.

## Result

**PARTIAL SUCCESS — hygiene-only delivery + analytical issue.**

* Priority 0: SUCCESS. Scanner regression resolved.
* Priority 1: SUCCESS. Aristotle slots freed.
* Priority 2: NOT ATTEMPTED — replaced with analytical issue
  documenting the strategy bug.

Compile is clean (`lake env lean OpenMath/Chapter5/Section515.lean`
exits 0; same warning profile as cycle 120). Tautology scanner
returns 0 hits in `Section515.lean`.

## Faithfulness check

No new `def`, `class`, `structure`, or `theorem` introduced this
cycle. The only file edits in `OpenMath/` are alpha-renames
(semantics-preserving) of three local hypotheses inside
`aux_515D_iterated_V_bound`. The capstone
`GeneralLinearMethod.stable_consistent_isConvergent` continues to
have only the cycle-116 pre-existing Frobenius divergence on
`IsConvergent` (already documented in
`glm_isconvergent_strengthened.md`). **No new faithfulness
divergence introduced this cycle.**

## Dead ends

### Strategy's Backup B2 has an unprovable residual claim

Spent ~30 minutes auditing the strategy's B2 path before deciding
not to code it. The "Step 3" residual statement
`sup_i |R m i| ≤ K_R · h²` is false in general — `localStepError_bound`'s
output `K` includes an `α · h · δ_max` term where `δ_max` is the
sup of the previous-step deviation. This term cannot be absorbed
into `K_R · h²` without circular reasoning (`δ_max` is unbounded
a priori).

The strategy's "Step 3 (a) stage-difference contribution: ...
bounded by `(stage-error-coefficient) · h_n` ... multiply by
`‖M.B‖_∞` to get `O(h_n²)`" is wishful — `aux_515B_eta_contraction`
explicitly gives `|η j| ≤ ell_U j · δ_max + h² L² M · phi_A j`,
so the stage error has a `δ_max`-proportional term that propagates
through `M.B`.

### Strategy's blacklist of `aux_515D_gronwall_bound` is too aggressive

The strategy claims the vectorial recurrence "does not produce a
sum-form bound naturally". This is incorrect: the cycle 120
iterated V bound, applied to the closed-form expansion
`δ(m) = V^m · δ(0) + Σ V^(m-1-k) · K(k)`, gives **uniform** `C₀`
factors (not `C₀^k`), and the sum
`Σ_{k<m} C₀ · |K(k)|` IS the sum-form input
`a + α'·h·Σ u(k) + β'·h²·m` that `aux_515D_gronwall_bound`
consumes. The cycle 118 dead end was about the *scalar*
per-step recurrence's `(V_norm + α·h)^n` blow-up, which is
genuinely an obstacle there but does NOT apply once we are in
the vectorial-with-iterated-V regime.

## Discovery

### Sum-form Grönwall is the right tool for the corrected outline

The corrected composition (per
`.prover-state/issues/cycle_121_strategy_B2_correction.md`) goes:

1. Per-step: `δ(m+1) = V·δ(m) + K(m)`,
   `|K(m) i| ≤ α·h·δ_max(m) + β·h²` (from `localStepError_bound`).
2. Closed-form: `δ(m) = V^m·δ(0) + Σ_{k<m} V^(m-1-k)·K(k)`
   (induction on `m`).
3. Sup bound (cycle 120): `sup_i |δ(m) i|
   ≤ C₀·u(0) + Σ_{k<m} C₀·(α·h·u(k) + β·h²)`.
4. Sum-form: `u(m) ≤ a + α'·h·Σ u(k) + β'·h²·m` with
   `a := (C₀ + C₀·α·h)·u(0)`, `α' := C₀·α`, `β' := C₀·β`.
5. Grönwall (`aux_515D_gronwall_bound`): closed form
   `u(n) ≤ exp(α'·(x-x₀))·a + (exp(α'·(x-x₀))-1)·(β'·h_n/α')`.
6. Repackage as `C_init·u(0) + C_lin·h_n`.

Total ~150 LOC, broken into ~5–7 sub-`have` blocks. Tractable in
a single cycle if planned carefully.

### `0 ≤ M.glmAbscissae v` should be provable internally

The strategy avoids `aux_515D_construct_ell_U_phi_A` because of
its `_hc_nn` hypothesis. But `localStepError_bound` needs
`_hc_nonneg : ∀ i, 0 ≤ c i` regardless. Cycle 122 should check
the `M.glmAbscissae v` definition (likely something like
`(M.A *ᵥ 1) i` or `(M.A · 1)`) and verify it is non-negative
under the existing convergence-context hypotheses (so we can
prove `_hc_nn` internally as a `have`, no upstream propagation
needed). This avoids the §513/§514 cascade risk.

## Suggested next approach

**Cycle 122 should**:

1. Read the corrected analytical outline in
   `.prover-state/issues/cycle_121_strategy_B2_correction.md`
   FIRST.
2. Verify the `M.glmAbscissae v` definition and check if
   `0 ≤ M.glmAbscissae v` is provable from existing hypotheses
   (Path A1) or requires upstream propagation (Path A2). Path A1
   is strongly preferred to avoid §513/§514 cascade risk.
3. Attempt the full vectorial composition (Path A in the
   correction issue) as the primary deliverable. ~150 LOC,
   modular in 7 sub-`have` blocks.
4. If Path A stalls, fall back to Path B in the correction issue:
   introduce a corrected per-step K-bound helper with `sorry`
   body (~80 LOC isolated), and write the outer composition
   (~70 LOC).
5. Do NOT propagate `_hc_nn` to
   `aux_515D_max_deviation_geometric_bound`'s signature (this is
   the original strategy's blacklist, still correct).
6. Do NOT use `aux_515D_per_step_recurrence` directly on the
   sup-norm — its scalar `(V_norm + α·h)^n` form blows up for
   stable but non-contracting V (cycle 118 dead end). Instead use
   `aux_515D_gronwall_bound` via the vectorial-with-iterated-V
   sum-form (corrected path).

## Cycle 121 deliverables summary

* `OpenMath/Chapter5/Section515.lean`: 6 alpha-rename edits
  (3 declarations + 3 calc-step closers in
  `aux_515D_iterated_V_bound`).
* `.prover-state/issues/tautology_scanner_false_positives.md`:
  appended cycle 121 update note (records the rename).
* `.prover-state/issues/cycle_121_strategy_B2_correction.md`:
  NEW issue file. Documents the analytical bug in the cycle 121
  strategy's Backup B2 path and provides a corrected ~150 LOC
  composition outline for cycle 122.
* `.prover-state/task_results/cycle_121.md`: this file.

No `lean_status.json` or `plan.md` updates: thm:515D remains
`partial` / `[~]`.
