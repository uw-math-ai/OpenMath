# Cycle 244 strategy — `lem:319A` Phase 1: stage/output difference recurrences

## §A — Aristotle-results inbox

Empty. No pending Aristotle results to incorporate. Aristotle path
not used this cycle (planning a structural Lean ship; no submission
recommended unless Phase 1 stalls).

## §B — Target

**`lem:319A` Phase 1** — Butcher §319 "Global truncation error
(RK)" lemma (p. 188).

The textbook lemma states:

> Let `f : ℝ^m → ℝ^m` satisfy a Lipschitz condition with constant
> `L`. Let `y₀, z₀ ∈ ℝ^m` be two input values to a step with the
> RK method `(A, b, c)`, using stepsize `h ≤ h₀` where
> `h₀ L ρ(|A|) < 1`, and let `y₁, z₁` be the corresponding output
> values. Then
>
>   `‖y₁ − z₁‖ ≤ (1 + h L^†) ‖y₀ − z₀‖`,
>
> where `L^† = L |b|^T (I − h₀ L |A|)^{−1} 𝟙`.

The textbook proof has **two structural inequalities** plus an
M-matrix inversion that derives the `L^†` constant. **Cycle 244
ships only the two structural inequalities** (Phase 1). The
`L^†` closed-form derivation requires inverting `(I − h₀ L |A|)`
via M-matrix machinery (currently only in
`OpenMath/Chapter5/MMatrix.lean`), which would create a
Chapter-3-imports-Chapter-5 cycle. Phase 2 (cycle 245+) handles
this either by relocating MMatrix or re-building the small piece
needed inline.

### Phase 1 deliverables (cycle 244)

Create new file `OpenMath/Chapter3/Section319.lean` with two
public theorems plus a bundled wrapper:

#### Deliverable D1 — stage-difference recurrence

```lean
theorem RKTableau.stage_diff_recurrence {s : ℕ} (M : RKTableau s)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {f : N → N} {L : ℝ} (hL : 0 ≤ L) (hf_lip : LipschitzWith L.toNNReal f)
    {y₀ z₀ : N} {h : ℝ} (hh : 0 ≤ h)
    {Y Z : Fin s → N}
    (hY_stage : ∀ i, Y i = y₀ + h • ∑ j, M.A i j • f (Y j))
    (hZ_stage : ∀ i, Z i = z₀ + h • ∑ j, M.A i j • f (Z j))
    (i : Fin s) :
    ‖Y i - Z i‖ ≤ ‖y₀ - z₀‖ + h * L * ∑ j, |M.A i j| * ‖Y j - Z j‖
```

Proof recipe:
1. Subtract `hY_stage i` from `hZ_stage i`:
   `Y i - Z i = (y₀ - z₀) + h • ∑ j, M.A i j • (f (Y j) - f (Z j))`.
2. Take norms; apply triangle inequality:
   `‖Y i - Z i‖ ≤ ‖y₀ - z₀‖ + ‖h • ∑ j, M.A i j • (f (Y j) - f (Z j))‖`.
3. Pull `h` out via `norm_smul` + `abs_of_nonneg hh`:
   `‖h • ⋯‖ = h * ‖∑ ⋯‖`.
4. Bound the sum norm via `norm_sum_le`:
   `‖∑ j, M.A i j • (f (Y j) - f (Z j))‖ ≤ ∑ j, ‖M.A i j • (f (Y j) - f (Z j))‖`.
5. Each summand: `‖M.A i j • (f (Y j) - f (Z j))‖
   = |M.A i j| * ‖f (Y j) - f (Z j)‖ ≤ |M.A i j| * (L * ‖Y j - Z j‖)`
   via `norm_smul`, `Real.norm_eq_abs`, plus
   `LipschitzWith.dist_le_mul` bridged to `Real.dist_eq`/`abs`-form.
6. Combine: `∑ j, |M.A i j| * (L * ‖Y j - Z j‖)
   = L * ∑ j, |M.A i j| * ‖Y j - Z j‖` via `← Finset.mul_sum`.
7. Multiply through by `h` and finish with `linarith`.

#### Deliverable D2 — output-difference recurrence

```lean
theorem RKTableau.output_diff_recurrence {s : ℕ} (M : RKTableau s)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {f : N → N} {L : ℝ} (hL : 0 ≤ L) (hf_lip : LipschitzWith L.toNNReal f)
    {y₀ z₀ y₁ z₁ : N} {h : ℝ} (hh : 0 ≤ h)
    {Y Z : Fin s → N}
    (hY_out : y₁ = y₀ + h • ∑ i, M.b i • f (Y i))
    (hZ_out : z₁ = z₀ + h • ∑ i, M.b i • f (Z i)) :
    ‖y₁ - z₁‖ ≤ ‖y₀ - z₀‖ + h * L * ∑ i, |M.b i| * ‖Y i - Z i‖
```

Proof recipe: identical to D1 with `(M.b i, y₁, z₁)` substituted
for `(M.A i j, Y i, Z i)`. The output formulae are *not implicit*
(no fixed-point recursion), so the proof skeleton is genuinely
shorter than D1 — same six steps without any sum-over-stage-index
gymnastics.

#### Deliverable D3 — bundled IsRKOneStep wrapper

```lean
theorem RKTableau.lem_319A_recurrences {s : ℕ} (M : RKTableau s)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {f : N → N} {L : ℝ} (hL : 0 ≤ L) (hf_lip : LipschitzWith L.toNNReal f)
    {y₀ z₀ y₁ z₁ : N} {h : ℝ} (hh : 0 ≤ h)
    (h_y : M.IsRKOneStep f y₀ h y₁) (h_z : M.IsRKOneStep f z₀ h z₁) :
    ∃ Y Z : Fin s → N,
      (∀ i, ‖Y i - Z i‖ ≤ ‖y₀ - z₀‖ + h * L * ∑ j, |M.A i j| * ‖Y j - Z j‖)
      ∧ ‖y₁ - z₁‖ ≤ ‖y₀ - z₀‖ + h * L * ∑ i, |M.b i| * ‖Y i - Z i‖
```

Body: destructure `h_y` to obtain `Y, hY_stage, hY_out`; destructure
`h_z` to obtain `Z, hZ_stage, hZ_out`. Apply D1 universally over
`i`, apply D2. Package as the existential.

#### Deliverable D4 — non-vacuity witness (mandatory)

Add at end of file, after the public deliverables:

```lean
example : ∀ (y₀ z₀ y₁ z₁ : ℝ) (h : ℝ) (hh : 0 ≤ h),
    paddedEuler.IsRKOneStep (fun y => y) y₀ h y₁ →
    paddedEuler.IsRKOneStep (fun y => y) z₀ h z₁ →
    ∃ Y Z : Fin 2 → ℝ,
      (∀ i, ‖Y i - Z i‖ ≤ ‖y₀ - z₀‖ + h * 1 * ∑ j, |paddedEuler.A i j| * ‖Y j - Z j‖)
      ∧ ‖y₁ - z₁‖ ≤ ‖y₀ - z₀‖ + h * 1 * ∑ i, |paddedEuler.b i| * ‖Y i - Z i‖
```

with `f := id : ℝ → ℝ` (Lipschitz with constant 1 via `LipschitzWith.id`).
Use `paddedEuler` (the canonical non-vacuity carrier from cycles
184+, `RKTableau 2`). If verification step (§L) reveals a different
single-stage exported tableau is preferred, swap.

## §C — Mathlib hook inventory

Hooks needed for D1/D2 (all expected present, but the worker
should `lean_local_search` to confirm exact names):

| Goal | Lemma | Notes |
|---|---|---|
| Triangle inequality on norm | `norm_add_le` | std |
| Difference of norms | `norm_sub_le` | std |
| Pull scalar out of norm | `norm_smul` | std |
| `‖h • x‖ = |h| * ‖x‖` for `h : ℝ` | `norm_smul` + `Real.norm_eq_abs` | std |
| `|h| = h` when `h ≥ 0` | `abs_of_nonneg` | std |
| `‖∑ x‖ ≤ ∑ ‖x‖` | `norm_sum_le` | std |
| Lipschitz bound | `LipschitzWith.dist_le_mul` | bridge `dist` ↔ `‖·‖` |
| `dist a b = ‖a - b‖` (norm space) | `dist_eq_norm` | std |
| Pull constant out of sum | `← Finset.mul_sum` | std |
| Sum manipulation | `Finset.sum_congr`, `Finset.sum_le_sum` | std |
| Final close | `linarith` / `ring` / `nlinarith` | std |

The `LipschitzWith L.toNNReal f` ↔ `‖f a - f b‖ ≤ L * ‖a - b‖`
bridge is the same one cycles 064 / 065 / 066 used heavily in §406B.
Look for an existing private helper in §406B / §515; if none, write
a 1-line helper inline. Pattern:

```lean
have habs : ‖f a - f b‖ ≤ L * ‖a - b‖ := by
  have := hf_lip.dist_le_mul a b
  simpa [dist_eq_norm, Real.coe_toNNReal _ hL] using this
```

## §D — File layout

**Create new file**: `OpenMath/Chapter3/Section319.lean`.

Imports needed (minimal):
```lean
import OpenMath.Chapter3.Section381   -- for RKTableau, IsRKOneStep, paddedEuler
import Mathlib.Topology.MetricSpace.Lipschitz  -- for LipschitzWith
import Mathlib.Analysis.Normed.Group.Basic  -- for norm_sum_le, norm_smul
```

If `paddedEuler` lives in a different module's namespace
(`OpenMath.Chapter3.Section312.RKTableau.paddedEuler` is likely),
qualify properly in the non-vacuity example.

**Aggregator update**: add `import OpenMath.Chapter3.Section319` to
`OpenMath/Chapter3.lean` if that aggregator file exists. Check via
`ls OpenMath/Chapter3*.lean`. If a flat module aggregator is in
place at `OpenMath.lean`, update there too.

## §E — Faithfulness check (run before commit)

For each new theorem (D1, D2, D3):

- [ ] Quote the entity `lem:319A` textbook statement (already
      reproduced in §B above) and identify which structural
      sub-claim each deliverable captures:
    * D1 ↔ Butcher's intermediate stage-difference inequality
      (proof, line 2 of `proof_text`).
    * D2 ↔ Butcher's intermediate output-difference inequality
      (proof, line 3 of `proof_text`).
    * D3 ↔ packaging of D1 + D2 against the `IsRKOneStep` predicate.
- [ ] **Documented divergence**: the headline `‖y₁ − z₁‖ ≤
      (1 + h L^†) ‖y₀ − z₀‖` form is **not** shipped in cycle 244.
      The `L^†` constant requires inverting `(I − h₀ L |A|)` via
      M-matrix machinery
      (`Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one` from
      `OpenMath/Chapter5/MMatrix.lean`, cycle 106), which is
      currently in Chapter 5 and would create a circular
      dependency if imported into Chapter 3. Phase 2 (cycle 245+)
      will either (a) relocate the MMatrix piece to a shared
      utility module, or (b) re-derive the needed M-matrix
      inversion inline in `Section319.lean` against just the
      Frobenius/L∞ norm bound `‖h₀ L |A|‖ < 1`. Either path is
      single-cycle work once D1/D2/D3 are landed.
- [ ] **Tautology check**: D1 and D2 conclusions are inequalities
      involving `‖Y i - Z i‖` / `‖y₁ - z₁‖`, not present as
      hypotheses. ✓
- [ ] **Identity check**: proofs are sequences of triangle
      inequality + Lipschitz bound + sum manipulation, not `exact h`. ✓
- [ ] **Hypothesis strength**:
    * `0 ≤ h` is unavoidable (the bound depends on `h`'s sign).
    * `0 ≤ L` is unavoidable (the bound is a multiple of `L`).
    * `LipschitzWith L.toNNReal f` is the textbook hypothesis
      verbatim.
    * `IsRKOneStep` matches Butcher's "input/output values to a
      step with method (A, b, c)".

  No extra hypotheses beyond the textbook. ✓
- [ ] `lean_status.json` row for `lem:319A`: status `unformalized`
      → `partial` (cycle 244 ships intermediate inequalities; the
      headline `(1 + h L^†)` form is deferred to Phase 2). Add a
      `lean_file: "OpenMath/Chapter3/Section319.lean"` and
      `lean_symbol: "RKTableau.lem_319A_recurrences"` entry.
- [ ] `plan.md` row for `lem:319A`: change `[ ]` → `[~]` with a
      one-line note: "Phase 1 (intermediate inequalities) shipped
      cycle 244; Phase 2 (L^† closed form via M-matrix inversion)
      deferred."

## §F — What NOT to try

* Do **NOT** attempt to derive the `L^†` closed form in cycle 244.
  The M-matrix inversion `(I − h₀ L |A|)^{−1}` is in
  `OpenMath/Chapter5/MMatrix.lean` (cycle 106), which Chapter 3
  cannot import without creating a circular dependency. If you
  attempt to inline it: the proof requires `Matrix.EntrywiseNonneg`
  + Neumann series infrastructure (~150 LOC) which dwarfs the
  cycle's deliverable bar.
* Do **NOT** introduce `axiom` or `constant`. The `L^†` constant
  is computable in principle (M-matrix inversion is constructive
  via the geometric series).
* Do **NOT** raise `maxHeartbeats` above 200000.
* Do **NOT** define a new `IsRKOneStep`-style predicate. Reuse the
  cycle 030 one in `Section381.lean` (line 924).
* Do **NOT** specialise to `f : ℝ → ℝ` (scalar). The textbook
  statement is for `ℝ^m`; our `IsRKOneStep` is generic over
  `[NormedAddCommGroup N] [NormedSpace ℝ N]`. Use that generality.
  The non-vacuity D4 *example* may specialise to `ℝ` for clarity.
* Do **NOT** edit `extraction/raw_text/` or
  `extraction/formalization_data/entities/`. Those are regenerated.
* Do **NOT** edit `scripts/autonomous_loop.py` (worker rule, per
  CLAUDE.md and standing `tautology_scanner_false_positives.md`
  issue).
* Do **NOT** attempt `cor:550C` (worker's cycle 243 fallback
  suggestion). It depends on `thm:550B`, which depends on
  `thm:550A`'s general-`n` closure (deferred per
  `thm_550A_general_n.md`; Aristotle cancelled at 21% in cycle 151).
* Do **NOT** attempt `thm:535A` (Underlying one-step method, GLM).
  Per `entities/thm_535A.json`, this requires tree-indexed B-series
  functions (`ξ`, `η`, `θ`) and induction on tree order — multi-cycle
  infrastructure not yet in place.
* Do **NOT** attempt `def:422B`. Same blocker — requires the LMM
  side of the §383 group infrastructure and tree-indexed mappings.
* Do **NOT** attempt `def:442A`. Requires Riemann-surface
  infrastructure for stability functions.

## §G — Risk register and mitigations

| Risk | Likelihood | Mitigation |
|---|---|---|
| R1: `paddedEuler` not the right non-vacuity carrier | low | Verify via §L. If `Section381.lean` exports a single-stage `explicitEulerLMM_RK` ≠ `paddedEuler`, prefer it. Worst case: any concrete `RKTableau s` instance with `s ≥ 1` works. |
| R2: `LipschitzWith.dist_le_mul` produces NNReal-tinged inequality | medium | The bridge `dist a b = ‖a - b‖` + `Real.coe_toNNReal _ hL` clears it. Look for the existing pattern in `OpenMath/Chapter4/Section406.lean` cycles 064–067 if needed (e.g. `joint_lipschitz_pair_bound` in §406). |
| R3: `norm_smul` with `h : ℝ` and `x : N` produces `‖h‖` instead of `|h|` | low | `Real.norm_eq_abs` is the bridge. Standard pattern. |
| R4: Sum-norm `‖∑‖ ≤ ∑‖·‖` lemma name drift | low | `norm_sum_le` is canonical; `Finset.norm_sum_le` is the alternate. Use `lean_local_search "norm_sum"`. |
| R5: GPFS slowness on the new file's first compile | low | New files have always compiled cleanly in cycles 222–243. The §441 GPFS pathology is specific to that file's heavy `Mathlib.Analysis.*` transitive load; `Section319.lean` only imports Section381 + a few light Mathlib modules. Expected compile time <10s. |
| R6: `Finset.sum_le_sum` in mid-proof needs an explicit pointwise hypothesis | low | Standard intro pattern: `apply Finset.sum_le_sum; intro j _; ...`. |
| R7: Confusion between `L : ℝ` (taken with `0 ≤ L`) and `L : ℝ≥0` (LipschitzWith's argument) | medium | Use the `(L : ℝ)` + `L.toNNReal` pattern that cycles 064–067 and 215+ have used successfully. The non-negativity `hL` is the bridge that lets `Real.coe_toNNReal _ hL` convert back. |
| R8: `Finset.mul_sum` direction — `c * ∑ f = ∑ c * f` or vice versa? | low | Try `Finset.mul_sum` first; if direction reversed, use `← Finset.mul_sum`. The `nlinarith`/`linarith` finishes will be tolerant. |

## §H — Exit criteria (in order, hard ABORT thresholds)

1. **D1 + D4 (non-vacuity for D1 only) shipped** ≤ 60 minutes of
   worker time → continue to D2.
2. **D2 shipped** in ≤ 30 minutes → continue to D3.
3. **D3 shipped** ≤ 15 minutes → finalise (faithfulness check,
   commit, lean_status.json, plan.md updates).

If D1 stalls past 60 minutes: **abort to fallback** (§I). Do NOT
introduce sorries to "ship" a scaffolded D1 (cycle 200 / cycle 201
precedent — sorry-first scaffolds with no path to single-cycle
closure get rolled back, costing a cycle).

If D1 ships but D2 stalls past 30 minutes: ship D1 + non-vacuity
witness only; reformulate the cycle deliverable as "Phase 1a" with
D2 deferred. Update lean_status.json accordingly (still `partial`,
but with a narrower scope note).

## §I — Fallback (only if D1 itself stalls)

Pivot to a **§383 elementary-weight algebra small win** analogous
to cycle 239 (`elementaryWeightQ_phi`). Specifically, ship one
small named lemma extending the §383 group's `elementaryWeightQ_phi`
interaction with `composeQ_phi` — e.g. an explicit zero-on-trivial-tree
corollary, or an `@[simp]` reduction lemma for `elementaryWeightQ_phi`
on a specific tree shape. Estimated 30–50 LOC, axiom-clean,
low-risk ship.

The fallback target should be:
```lean
@[simp] theorem elementaryWeightQ_phi_paddedEuler_vertex :
    elementaryWeightQ_phi ⟦⟨2, paddedEuler⟩⟧ RootedTree.vertex = 1
```
or similar — a concrete numerical witness for cycle 239's lift on a
non-trivial method. This is strictly bonus content (0 sorries,
small LOC, builds on cycle 239's infrastructure).

## §J — Commit message template

```
Cycle 244 — §319 lem:319A Phase 1 (stage/output difference recurrences) SHIPPED.

New file OpenMath/Chapter3/Section319.lean (~120 LOC, 0 sorries):
* RKTableau.stage_diff_recurrence — Lipschitz-bound stage-by-stage
  difference recurrence for two RK steps from distinct inputs.
* RKTableau.output_diff_recurrence — Lipschitz-bound output-difference
  recurrence given the stage tuples.
* RKTableau.lem_319A_recurrences — bundled existential form against
  IsRKOneStep witnesses.
* Non-vacuity witness on paddedEuler with f := id.

All declarations axiom-clean ([propext, Classical.choice, Quot.sound]).

Faithfulness divergence: the headline (1 + h L^†) bound from
Butcher's lem:319A statement requires inverting (I − h₀ L |A|) via
M-matrix machinery currently in Chapter 5. Phase 2 (relocating or
re-deriving the M-matrix inversion) deferred to cycle 245+.

lean_status.json: lem:319A unformalized → partial.
plan.md: lem:319A [ ] → [~] with Phase 1/2 split note.
```

## §K — Why this target now

* Worker's cycle 243 task results explicitly recommended `lem:319A`
  as primary target with `cor:550C` as fallback. Dependencies
  (def:110A, lem:110B, thm:110C) are all formalized in Chapter 1,
  and `IsRKOneStep` from cycle 030 + `paddedEuler` from cycle 184
  supply the structural carriers.
* `cor:550C` is blocked (depends on thm:550B which depends on
  thm:550A general-n closure, deferred per `thm_550A_general_n.md`).
* Other Chapter-3 / Chapter-4 candidates (`thm:535A`, `def:422B`,
  `def:442A`, `def:388D`) all require multi-cycle tree-indexed
  function infrastructure that is not yet in place.
* Phase 1 is structurally complete — Butcher's proof literally
  consists of these two intermediate inequalities plus the
  M-matrix inversion. Shipping Phase 1 alone constitutes
  substantive textbook capture with a clear documented divergence.
* The §523 (cycles 241–243) momentum has run its natural course
  (identity → residual → inequality is a complete three-form
  story); pivoting to a fresh chapter avoids over-cycling.
* `Section319.lean` is a clean greenfield file — no GPFS pathology
  risk (the §441 issue is file-specific to that file's Mathlib
  transitive-load profile, not a global cluster issue).

## §L — Note A: which RK tableau to use for the non-vacuity witness

Quick verification step at the start of cycle 244:
```bash
grep -n "^def \(explicitEuler\|paddedEuler\)" OpenMath/Chapter3/Section381.lean
grep -n "^noncomputable def \(explicitEuler\|paddedEuler\)" OpenMath/Chapter3/Section381.lean
```

Pick whichever single-stage (or two-stage) RK tableau is exported
publicly. The non-vacuity witness only requires that *some* concrete
`RKTableau` exists; the choice does not affect the soundness of D1/D2/D3.

If the file exports `paddedEuler : RKTableau 2`, use it (consistent
with cycles 184–243's non-vacuity carrier). The 2-stage zero
channel collapses cleanly under `f := id`, so the stage-diff
recurrence holds vacuously on the second stage.

If the file exports a single-stage `explicitEuler : RKTableau 1`
(cycle 030), prefer it for cleaner unfolding in the example body.

## §M — Updated cycle 245+ outlook

After cycle 244 lands D1/D2/D3:

* **Cycle 245**: Phase 2 — derive the headline `‖y₁ − z₁‖
  ≤ (1 + h L^†) ‖y₀ − z₀‖` form via M-matrix inversion. Two
  approaches:
  - **Option α (recommended)**: relocate `OpenMath/Chapter5/MMatrix.lean`
    to a chapter-neutral location like `OpenMath/MMatrix.lean`,
    update Section515 imports. Minimal disruption (it's a leaf
    utility module).
  - **Option β**: re-derive the needed `(I − h₀ L |A|)^{−1}`
    inversion inline in `Section319.lean` using the same
    `hasSum_geom_series_inverse` Neumann-series argument as
    cycle 106's MMatrix lemma. ~80 LOC, more code but isolates
    the inversion to where it's used.

* **Cycle 246+**: `thm:319B` (Global truncation error bound via
  local error accumulation) — the headline §319 theorem that
  consumes `lem:319A`. Likely requires Picard–Lindelöf solution
  existence (already partially formalised in
  `OpenMath/Chapter1/Section110.lean`; see
  `picard_lindelof_bound_strengthening.md` for the standing gap).

The §319 cluster (lem:319A + thm:319B) is the natural
prerequisite for the §322–§324 RK order-condition theorems that
are still `[ ]` in the plan, so this cycle's Phase 1 ship has
significant downstream value.
