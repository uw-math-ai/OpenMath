# Cycle 106 Strategy

## Status snapshot

* **Sorries**: 1 in `OpenMath/` (`Section515.lean:995`,
  `aux_515B_eta_contraction`, deferred per
  `.prover-state/issues/lem_515B_eta_contraction_deferred.md`).
* **Aristotle**: TWO projects are `IN_PROGRESS` at 4–6 %:
  - `4688b630-d9c9-4f86-9572-7e4bd9a6b0b8` (cycle 103 batch for the
    full η-contraction): 6 % after >40 hours. Stuck. Treat as dead.
  - `8e9eec37-2285-439b-b8b9-cd116e58534c` (cycle 105 batch for
    `EntrywiseNonneg.inv_one_sub_of_norm_lt_one` via Neumann series):
    4 % after ~30 minutes. Too early to be useful.
  Both polled at planner time (2026-05-03 18:44 UTC).
* **MMatrix.lean** (cycle 105) provides 8 closure lemmas for the
  `EntrywiseNonneg` predicate. The load-bearing inverse-positivity
  lemma is documented in the trailing docstring but **not stubbed**
  (no `sorry`).
* **Recent cycle pattern** (CRITICAL):
  - Cycles 100 (-2) and 103 (-2): scaffold cycles that opened sorries
    without closing enough. **Negatively scored**.
  - Cycles 101/102/104 (+2 each), 105 (+1): focused work that did
    not net-add sorries.
  - **Lesson**: do NOT add new sorries to `OpenMath/` unless you can
    close at least as many in the same cycle. If a sub-target is
    too hard, leave it as a docstring TODO (as cycle 105 did) rather
    than a stub.

## Priority 0 — Aristotle polls (MANDATORY, ONE call each, 5 min total)

You MAY poll each Aristotle project once at the start of the cycle
to update yourself. Both are expected to still be IN_PROGRESS:

```
mcp__aristotle__get_status project_id="8e9eec37-2285-439b-b8b9-cd116e58534c"
mcp__aristotle__get_status project_id="4688b630-d9c9-4f86-9572-7e4bd9a6b0b8"
```

* **If `8e9eec37-...` returned a proof** for inverse-positivity:
  download/extract it via `mcp__aristotle__extract_result`, vendor
  the proof into `OpenMath/Chapter5/MMatrix.lean` (replacing the
  trailing docstring TODO with a real lemma), verify with
  `lake build OpenMath.Chapter5.MMatrix`, then proceed to Priority 2.
* **If `4688b630-...` returned a proof** for `aux_515B_eta_contraction`:
  vendor it into `Section515.lean:995`, verify, run `#print axioms`,
  and you're done — proceed to Priority 4 (housekeeping) and skip
  Priorities 1–3.
* **If both still IN_PROGRESS**: proceed to Priority 1.
* **Do NOT poll a second time** in this cycle. CLAUDE.md is explicit.

## Priority 1 — Manually prove `EntrywiseNonneg.inv_one_sub_of_norm_lt_one` (REQUIRED)

**Where**: `OpenMath/Chapter5/MMatrix.lean`, replacing the trailing
docstring "Deferred to cycle 106" block (lines ~165–186) with a real
lemma. Keep the existing 8 closure lemmas above unchanged.

**Statement** (target):

```lean
section InversePositivity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Neumann series: for an entrywise-nonneg matrix `M` over ℝ with
operator norm `‖M‖ < 1`, the inverse `(1 - M)⁻¹` is entrywise
non-negative. The proof goes via the Neumann series
`(1 - M)⁻¹ = ∑' k, M^k`. -/
lemma EntrywiseNonneg.inv_one_sub_of_norm_lt_one
    {M : Matrix n n ℝ} (hM : M.EntrywiseNonneg)
    (h_norm : ‖M‖ < 1) :
    (Ring.inverse ((1 : Matrix n n ℝ) - M)).EntrywiseNonneg := by
  sorry  -- close in this cycle, do not commit with a sorry

end InversePositivity
```

Notes:

1. Use `Ring.inverse`, **not** `Matrix.inv` / `(·)⁻¹`. `Ring.inverse`
   is the normed-ring inverse and is the codomain of the Mathlib
   geometric-series lemma we need. `Matrix.inv` requires nonsingularity
   and is harder to wire up.
2. The matrix norm here is `‖M‖` from the `NormedRing` instance on
   `Matrix n n ℝ` (operator-2-norm or one of the equivalent ones in
   `Mathlib.Analysis.Matrix`). It does **not** matter which norm — any
   normed-ring norm with `‖M^k‖ ≤ ‖M‖^k` works for the Neumann
   argument. Mathlib provides `Matrix.normedRing` automatically when
   the entry type is normed.

**Proof sketch** (use this; do not freelance):

* Mathlib lemma: `NormedRing.inverse_one_sub` or
  `tsum_geometric_of_norm_lt_one` (search via `lean_local_search` or
  `lean_loogle "Ring.inverse (1 - _) = _"`). Whatever returns, it
  should give a `HasSum (fun k => M^k) (Ring.inverse (1 - M))` shape
  under `‖M‖ < 1`.
* Convert `HasSum` to entrywise convergence via
  `Matrix.hasSum_iff` or by applying `Matrix.entrywise_eval` to both
  sides — for each `(i, j)`, `HasSum (fun k => (M^k) i j) ((Ring.inverse (1 - M)) i j)`.
* Each summand `(M^k) i j ≥ 0` by `EntrywiseNonneg.pow hM k i j`.
* Therefore the limit `(Ring.inverse (1 - M)) i j ≥ 0` by
  `hasSum_nonneg` or `tsum_nonneg`.

**If you cannot find `NormedRing.inverse_one_sub`** in Mathlib, search
under these alternative names (one of these is the right name as of
Mathlib v4.28):

* `NormedRing.tsum_geometric_of_norm_lt_one`
* `NormedRing.inverse_one_sub_eq_tsum`
* `Units.oneSub` (the `IsUnit (1 - x)` from `‖x‖ < 1`)
* `IsUnit.inverse_geom_series`

Recommended search calls (use `lean_loogle`, NOT `lean_leansearch` —
the latter is too slow for type-pattern queries):

```
lean_loogle "?M : Matrix _ _ ℝ → ‖?M‖ < 1 → IsUnit (1 - ?M)"
lean_loogle "‖?x‖ < 1 → HasSum (fun k => ?x ^ k) _"
lean_loogle "Ring.inverse (1 - ?x)"
lean_local_search "geom"
lean_local_search "Neumann"
```

**Boundary**: `n = Type*` with `Fintype n` `DecidableEq n` (NOT
restricted to `Fin s`). Matches Mathlib's normed-ring instance on
`Matrix n n ℝ` and is what the η-contraction will need.

**If the Mathlib lemma applies to `Ring.inverse` but the η-contraction
needs `Matrix.inv`**: add a small bridge lemma after this one,

```lean
lemma EntrywiseNonneg.matrix_inv_one_sub_of_norm_lt_one
    {M : Matrix n n ℝ} (hM : M.EntrywiseNonneg) (h_norm : ‖M‖ < 1) :
    ((1 : Matrix n n ℝ) - M)⁻¹.EntrywiseNonneg
```

via `Matrix.inv_eq_ring_inverse` (verify with `lean_local_search`)
or by showing `IsUnit (1 - M)` (from `Units.oneSub`) gives
`(1 - M)⁻¹ = Ring.inverse (1 - M)`. **Defer this bridge to cycle 107
if the search churns** — Priority 1 is already a substantial deliverable.

**Hard ceiling for this priority**: 60 minutes / ~80 LOC. If you cannot
close the proof, do NOT commit a `sorry` — leave the docstring TODO
in place and move to Priority 4 (the cycle still has the cycle 105
infrastructure to credit).

## Priority 2 — Comparison lemma for M-matrix monotonicity (REQUIRED if Priority 1 lands)

**Where**: `OpenMath/Chapter5/MMatrix.lean`, after the inverse-positivity
lemma in the same `InversePositivity` section.

**Statement**:

```lean
/-- **M-matrix comparison principle**: if `M ≥ 0` (entrywise) with
`‖M‖ < 1`, and `(1 - M)·v ≥ 0` (entrywise, where `0` is the zero
function), then `v ≥ 0`. -/
lemma EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg
    {M : Matrix n n ℝ} (hM : M.EntrywiseNonneg) (h_norm : ‖M‖ < 1)
    {v : n → ℝ} (h : ∀ i, 0 ≤ ((1 - M) *ᵥ v) i) :
    ∀ i, 0 ≤ v i := by
  sorry  -- close in this cycle, do not commit with a sorry
```

**Proof**: `v = (1 - M)⁻¹ · ((1 - M) · v)`, so `v` is the action of
an entrywise-nonneg operator on a non-negative vector, which is
non-negative. Concretely:

1. From `h_norm`, `IsUnit ((1 : Matrix n n ℝ) - M)` via `Units.oneSub`
   or analogous.
2. Hence `(1 - M)⁻¹ * (1 - M) = 1` (or via `Ring.inverse_mul_cancel`).
3. So `v = (1 - M)⁻¹ *ᵥ ((1 - M) *ᵥ v)`.
4. Apply `EntrywiseNonneg.mulVec_nonneg` (cycle 105) with the
   inverse-positivity from Priority 1.

**Generalization** (only if the proof falls out cleanly; otherwise
skip): the two-vector form

```lean
lemma EntrywiseNonneg.mulVec_le_of_one_sub_mulVec_le
    {M : Matrix n n ℝ} (hM : M.EntrywiseNonneg) (h_norm : ‖M‖ < 1)
    {u v : n → ℝ} (h : ∀ i, ((1 - M) *ᵥ u) i ≤ ((1 - M) *ᵥ v) i) :
    ∀ i, u i ≤ v i
```

is the "subtract" form of the same principle and is what
`aux_515B_eta_contraction` actually consumes. It follows from the
non-negativity form by setting `w := v - u`.

**Hard ceiling**: 30 minutes / ~30 LOC (after Priority 1 is in place).

## Priority 3 — Close `aux_515B_eta_contraction` (STRETCH; conditional on Priorities 1+2)

**Only attempt this if Priorities 1 and 2 both land cleanly with
**zero** added sorries.** If either falters, defer this priority to
cycle 107 — landing the Mathlib infrastructure alone with no new
sorries is already a +1 cycle.

**Where**: `OpenMath/Chapter5/Section515.lean:973-995`.

**Signature change** (REQUIRED): add a hypothesis
`(h_norm_h₀LA : ‖h₀ • L • |A|‖ < 1)` or equivalently
`(h_norm : ‖((h₀ * L) : ℝ) • A.map (|·|)‖ < 1)` — pick whichever
matches the Mathlib `Matrix.map` / scalar-multiplication API more
closely. This is a **faithfulness divergence** (the textbook tacitly
assumes "h₀ small enough"); document in the lemma's docstring with
a pointer to `lem_515B_eta_contraction_deferred.md`. Update that
issue file's "Status" header to "RESOLVED — closed cycle 106 with
explicit `‖h₀L|A|‖ < 1` hypothesis" if the closure lands.

**Update the unique downstream consumer** (`localStepError_bound`,
~line 993) to either supply this hypothesis or carry it through to
its own caller. Verify by grep — `aux_515B_eta_contraction` is
`private`, so it is only invoked locally.

**Proof outline** (translate the §B "Mathematical argument" block of
the deferred-issue file into Lean):

1. From `_hcontraction`, derive
   `∀ j, |η j| ≤ Σ_k|U_{jk}|·δ_max + h*L*Σ_k|A_{jk}|·|η_k| + h²L²M·(½c_j² + Σ|A_{jk}·c_k|)`
   via `abs_sub_abs_le_abs_sub` / triangle and `_hδ_max`.
2. Set `target_j := ell_U j · δ_max + h²L²M · phi_A j`. Show
   `(I - h₀L|A|)·target = Σ|U|·δ_max + h²L²M·(½c² + |A·c|)` using
   `_hellU_eq` and `_hphiA_eq`. (This is a per-row algebraic identity,
   should be `linear_combination` or `ring`-style.)
3. Show that `(I - hL|A|)·|η|` ≤ `(I - h₀L|A|)·target` per row. Use
   `_hh_le : h ≤ h₀` plus non-negativity of `target` and `|A|`.
4. Apply Priority 2's comparison lemma with `M := h • L • |A|.map (|·|)`
   (operator), `u := |η|`, `v := target`. Discharge `‖h • L • |A|‖ < 1`
   from `h ≤ h₀` and `h_norm_h₀LA`.

**Hard ceiling**: 90 minutes / ~120 LOC. If you exceed either, abort
and commit Priorities 1–2 only (no `sorry` regression).

## Priority 4 — Housekeeping (always; quick)

* If Priority 3 closes: update
  `extraction/formalization_data/lean_status.json` for the relevant
  515B entities (set `lean_status` to `formalized`, populate
  `lean_files`).
* Update `.prover-state/issues/lem_515B_eta_contraction_deferred.md`
  with a "Status (cycle 106)" block — RESOLVED if Priority 3 closes,
  PARTIAL if only Priorities 1–2 land.
* Write `.prover-state/task_results/cycle_106.md` per the CLAUDE.md
  template.
* Final `#print axioms` checks on every theorem touched. Should be
  exactly `[propext, Classical.choice, Quot.sound]`. Run
  `lake build OpenMath.Chapter5.MMatrix` BEFORE the axiom check (per
  cycle 072 lesson — `lake env lean <file>` does NOT update the
  `.olean` cache, so axiom checks against an uncached `.olean`
  produce stale `sorryAx` false positives).

## What NOT to try (explicitly)

* **Do NOT introduce ANY new sorry to `OpenMath/`.** Priority 1's
  lemma is "close-or-leave-the-docstring-TODO". Priority 2 likewise.
  Priority 3 is "close-or-defer". The supervisor penalizes net-positive
  sorry deltas; cycle 105 set the precedent.
* **Do NOT poll Aristotle more than once per project.** CLAUDE.md is
  explicit; cycle 105 followed it correctly.
* **Do NOT re-submit Aristotle batches** for the same target.
  Submission `8e9eec37-...` is fresh; let it run. Submission
  `4688b630-...` is stale (>40 hours); cancel via
  `mcp__aristotle__cancel_project` ONLY if you need the slot for a
  new batch — otherwise leave it.
* **Do NOT use `Matrix.PosSemidef`.** It is the spectral / Loewner
  notion (`xᵀMx ≥ 0`), NOT entrywise non-negativity. The cycle 105
  `MMatrix.lean` docstring documents this distinction; do not blur it.
* **Do NOT widen `EntrywiseNonneg` to a typeclass** or to a more
  general `OrderedAddCommMonoid` framework. The cycle 105 sectioning
  (`Zero` / `AddCommMonoid` / `OrderedSemiring`) is intentional.
* **Do NOT raise `maxHeartbeats`** above 200000.
* **Do NOT modify `scripts/autonomous_loop.py`** — that is loop-
  maintainer territory.
* **Do NOT pivot to a new theorem (`lem:515C`, `thm:515D`, etc.)
  this cycle.** The cycle 105 task results suggested this as a
  "stretch" but it is conditional on closing `aux_515B_eta_contraction`
  first. With Priorities 1–3 above, this cycle has plenty of work.
* **Do NOT generalize the Neumann argument to non-archimedean fields
  / `NormedRing` over ℂ** "for future-proofing." Stay scalar-real.
* **Do NOT freelance an alternate proof of `aux_515B_eta_contraction`
  that bypasses the inverse-positivity / comparison principle.** I
  considered Picard iteration, comparison via partial order over
  Finset, and direct algebraic manipulation in the planning pass —
  all hit a wall at "(I − M) injective on the non-negative cone",
  which is exactly what M-matrix theory provides. The plan above is
  the canonical mathematical path; do not deviate.

## Build commands (for reference)

```bash
# After editing MMatrix.lean:
lake build OpenMath.Chapter5.MMatrix

# After editing Section515.lean (Priority 3):
lake build OpenMath.Chapter5.Section515

# Axiom check on a top-level theorem (must come AFTER lake build):
echo '#print axioms OpenMath.Chapter5.Section515.LinearMethod.localStepError_bound' | \
  lake env lean --stdin /dev/stdin
```

## Success criteria

* **Minimum (score ≥ 0)**: Aristotle polled, no new sorries committed,
  cycle 105 infrastructure remains intact, task_results written.
  This is achieved even if Priority 1 turns out infeasible.
* **Good (score +1)**: Priority 1 closes (inverse-positivity lemma
  proved), Priority 2 lands or is deferred to cycle 107, no sorry
  regression.
* **Excellent (score +2)**: Priorities 1+2 both close, no sorry
  regression. The η-contraction is now one cycle from closure.
* **Outstanding (score +3, very unlikely in one cycle)**: All three
  priorities close, sorry count in `OpenMath/` drops to **0**, and
  cycle 107 can pick up `lem:515C` or `thm:515D` directly.

## Cycle-107 preview (so cycle 106 doesn't over-scope)

If cycle 106 closes Priorities 1+2 only (most likely outcome), cycle
107 takes Priority 3 (close `aux_515B_eta_contraction`) as its sole
target, plus the housekeeping. That is a perfectly fine +2 cycle on
its own.

If cycle 106 closes all three priorities, cycle 107 opens
`thm:515D` ("Stability and consistency imply convergence") — the
direct downstream consumer of `lem:515B`. Per
`entities/thm_515D.json`, this is a substantial multi-cycle target,
so cycle 107 would scaffold sorry-first per CLAUDE.md.
