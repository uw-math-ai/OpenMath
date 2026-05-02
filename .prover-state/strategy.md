# Cycle 066 Strategy — §406D recurrence cluster non-autonomous lift

## TL;DR

Cycle 065 closed the §406B sub-lemma cluster non-autonomous lift
(joint-Lipschitz form, `L · M ↦ L_joint · (1 + M_bound)`
re-parameterisation). All six deliverables landed cleanly; build is
green; the only remaining sorry is the cycle 068 target
(`stable_consistent_isConvergent`, line 4552).

**Cycle 066 task: lift the §406D recurrence cluster.** Specifically
the five helpers that are consumed by
`stable_consistent_isConvergent_autonomous` (lines 4403–4531) just
above the cycle 065 §406B helpers:

* `T1_bound` (line 1180)
* `T2_bound` (line 1199)
* `T3_bound` (line 1239)
* `LinearMultistepMethod.globalError_recurrence_bound` (line 1268)
* `LinearMultistepMethod.globalError_recurrence_bound_textbook` (line 1331)

This is cluster 2 of the four-cluster lift roadmap in
`.prover-state/issues/non_autonomous_lift_plan.md`. Cluster 3
(squeeze helpers, ~100 lines) is cycle 067; cluster 4 (close
`stable_consistent_isConvergent` from the autonomous theorem +
adapters) is cycle 068.

---

## Step 1 (mandatory, ~5 min): Aristotle status check on cycle 065 submission

Cycle 065 left a single Aristotle project pending — alternative-proof
attempts for `residual_bound_nonauto` and `deriv_diff_bound_nonauto`.

**Project ID**: `55543850-b9f1-4dab-9d34-e65f732f030c`
**File**: `.prover-state/aristotle_submissions/cycle_065/project_ids.txt`
**Submitted**: cycle 065, ~30+ minutes ago by now.

Run **once**:

```
mcp__aristotle__get_status with project_id "55543850-b9f1-4dab-9d34-e65f732f030c"
```

* If `IN_PROGRESS` and < 50 %: skip — proceed straight to Step 2. Do
  NOT re-poll mid-cycle.
* If `IN_PROGRESS` and ≥ 50 %: still skip — Aristotle's contribution
  here is *alternative* proofs (we already have manual ones), not
  load-bearing.
* If `COMPLETED` and proofs returned: extract via
  `mcp__aristotle__download_result`. Compare against the manual
  cycle 065 proofs at `Section404.lean:4129` and `:4220`. Replace
  ONLY if the Aristotle proof is materially shorter (≥ 30 % fewer
  lines) AND the axiom check is clean AND it does not introduce new
  hypotheses. Otherwise keep the manual proofs (they are mechanical
  joint-Lipschitz + integral algebra; reproducibility wins).
* If `FAILED`: ignore. Move on.

**Do not** submit new Aristotle jobs at this step. Cycle 066's
Aristotle submission (Step 4) is a separate batch.

---

## Step 2 (main deliverable, ~150–200 lines): lift §406D recurrence cluster

The five autonomous helpers and their non-autonomous targets:

| # | Autonomous (line) | Non-autonomous target | Notes |
|---|---|---|---|
| 1 | `T1_bound` (1180) | `T1_bound_nonauto` | Lipschitz at one time arg only — pure rewrite |
| 2 | `T2_bound` (1199) | `T2_bound_nonauto` | Same as T1: Lipschitz at one time arg per summand |
| 3 | `T3_bound` (1239) | `T3_bound_nonauto` | Trivial: wrapper of cycle 065's `localTruncationError_bound_nonauto` |
| 4 | `globalError_recurrence_bound` (1268) | `globalError_recurrence_bound_nonauto` | Composes T1/T2/T3; `globalError_decomposition` already non-autonomous-friendly via `IsLMMSolution h x₀ f Y` |
| 5 | `globalError_recurrence_bound_textbook` (1331) | `globalError_recurrence_bound_textbook_nonauto` | Composes (4) + `(1 − h L |β₀|)`-inversion algebra; mechanical |

### Hypothesis form (mirror cycle 065)

For each `_nonauto` lift, take the same joint-Lipschitz pair the
cycle 065 helpers already consume:

```lean
{f : ℝ → ℝ → ℝ} {L_joint M_bound : ℝ}
(hL_joint : 0 ≤ L_joint) (hM : 0 ≤ M_bound)
(hf_lip : LipschitzWith L_joint.toNNReal (Function.uncurry f))
{yex : ℝ → ℝ}
(hyex_C1 : ContDiff ℝ 1 yex)
(hyex_ode : ∀ t, deriv yex t = f t (yex t))
(hf_yex_bound : ∀ t, |f t (yex t)| ≤ M_bound)
```

The `IsLMMSolution` hypothesis becomes
`hY : M.IsLMMSolution h x₀ f Y` (no `fun _ y => f y` wrapping —
non-autonomous from the outset).

### Bound shape (mirror cycle 065's `L · M ↦ L_joint · (1 + M_bound)`)

For T1/T2: the bound `h * L * |β| * |a − b|` becomes
`h * L_joint * |β| * |a − b|` (no `M_bound` shift; T1/T2 only use
Lipschitz, no `M_bound`). The Lipschitz application is

* T1 case: `|f a₁ a − f a₂ b|` where `a₁` and `a₂` differ by `i·h`.
  Bound: `L_joint · (|a₁ − a₂| + |a − b|)` via cycle 065's
  `joint_lipschitz_pair_bound` (line 4101). The `|a₁ − a₂|` term
  introduces a new `i·h` factor, so the bound shape becomes
  `h · L_joint · |β₀| · (i·h + |a − b|)`.
* T2 case: same pattern per summand.

**Decision point on bound shape — verify before writing the lift.**
Inspect the call sites of T1 and T2 inside
`globalError_recurrence_bound` (line 1268) and the upstream
`globalError_decomposition` (line 1094). Specifically:

* T1 is invoked at line 1302 with arguments
  `yex (x₀ + (n : ℝ) * h)` and `Y n`. **Both** `f`-applications
  inside T1 evaluate at the same time argument
  `t = x₀ + (n : ℝ) * h` in the non-autonomous case (T1's body
  computes `|h * β₀ * (f a − f b)|` where `a, b` are spatial values
  at the *same* time `t`, the current step). So T1's lift uses
  `lipschitzInSecond_univ_toLipschitzWith` (line 3862) at a single
  time argument — no joint-Lipschitz expansion needed, no extra
  time factor in the bound. Bound shape is identical to autonomous
  with `L ↦ L_joint`.
* T2 is invoked at line 1304 with per-`i` arguments
  `yex (x₀ + ((n − (i.val + 1)) : ℕ) : ℝ) * h)` and
  `Y (n − (i.val + 1))`. **Both** `f`-applications in T2's
  per-summand bound evaluate at the same time
  `t_i = x₀ + ((n − (i+1)) : ℕ : ℝ) * h` (the `(n − (i+1))`-th
  step time). So per-summand T2 also uses
  `lipschitzInSecond_univ_toLipschitzWith` at a single time arg.
  Bound shape: identical to autonomous with `L ↦ L_joint`.

**Re-confirm the above by reading lines 1199–1235 (T2_bound body) and
the call site at 1304** before writing the lift. If the inspection
contradicts the analysis above, fall back to the joint-Lipschitz
triangle expansion via `joint_lipschitz_pair_bound` and absorb the
extra `|t₁ − t₂|` term into the existing bound shape (it cleanly
factors out as a multiple of `h`, raising the bound order by a
controllable amount).

For T3: the bound is exactly cycle 065's
`localTruncationError_bound_nonauto`, so T3's lift is a one-line
`exact M.localTruncationError_bound_nonauto …` mirroring the
autonomous T3 (line 1252). The `L · M_bound` term becomes
`L_joint · (1 + M_bound)` automatically (inherited from cycle 065).

For (4) and (5): mechanically combine T1/T2/T3 via the same
`abs_add_le` + `add_le_add` chain the autonomous proofs use. Do
NOT re-derive — copy the autonomous structure and substitute the
`_nonauto` helpers.

### Faithfulness flags

Each new `_nonauto` lemma must carry a docstring noting:

* The autonomous version is preserved (cycle 040–044 helpers stay).
* The bound shape is `L_joint` in place of `L` (and `(1 + M_bound)`
  in place of `M_bound` for `T3_bound`'s LTE term, inherited from
  cycle 065).
* The non-autonomous form is the textbook 406D primary form;
  the autonomous version is the cycle 062 IVP-form variant.

### Implementation order (bottom-up)

Land in this order to keep the build green at every step:

1. `T3_bound_nonauto` (~5 lines, trivial wrapper).
2. `T1_bound_nonauto` (~25 lines, single
   `lipschitzInSecond_univ_toLipschitzWith` application — the time
   args coincide, see analysis above).
3. `T2_bound_nonauto` (~40 lines, sum-form of T1).
4. `globalError_recurrence_bound_nonauto` (~50 lines, mechanical
   composition mirroring autonomous version).
5. `globalError_recurrence_bound_textbook_nonauto` (~60 lines,
   mechanical inversion mirroring autonomous version).

**After each step, run `lake env lean OpenMath/Chapter4/Section404.lean`
and verify exit 0 before proceeding.**

### Ceiling

Per the cycle 060 red-flag threshold (~430 lines triggered a
regression), keep cycle 066's added LOC under 250. If T1/T2 require
the joint-Lipschitz triangle expansion (i.e. the time-args-coincide
analysis is wrong at the call site), defer (4) and (5) to cycle
067 and use the saved budget on Aristotle submissions instead.

**Hard line**: if (1)+(2)+(3) take > 150 lines, STOP, commit just
those three, and defer (4)+(5) to cycle 067. The cycle 060
regression was driven by cramming too much into one cycle; do not
repeat.

---

## Step 3 (mandatory, ~5 min): pre-commit faithfulness check

Run the CLAUDE.md checklist for every new `_nonauto` lemma:

* **Tautology check**: each conclusion is a real bound, not a
  hypothesis.
* **Identity check**: each proof composes the cycle 065 helpers + the
  autonomous proof structure; not `exact h_<name>`.
* **Hypothesis strength check**: joint Lipschitz on `Function.uncurry f`
  is the natural non-autonomous analogue; document in docstring.
* **Absent theorem check**: no comments promising lemmas not present.

Then build the full file:

```bash
lake env lean OpenMath/Chapter4/Section404.lean
```

Expect exit 0 with the single sorry at line 4552 (`stable_consistent_isConvergent`)
unchanged.

---

## Step 4 (optional, parallel to Step 2): Aristotle batch submission for cycle 067

If Step 2 finishes with budget remaining, prepare a self-contained
single-file Aristotle submission for the **cycle 067** squeeze cluster:

* The cluster is `globalError_outer_squeeze_a_term` (line 2311) and
  `globalError_outer_squeeze_c_term` (line 2383), plus the
  Tendsto-wrapper helpers (`bOf_tendsto_at_zero`, `cOf_tendsto_at_zero`,
  `aOf_tendsto_zero`, `bOf_limit_pos`).
* These are *pure ℝ-analysis squeeze arguments* — exactly the type
  Aristotle has historically handled well.
* Bundle them into
  `.prover-state/aristotle_submissions/cycle_066/squeeze_lifts.lean`
  with the cycle 065 helpers (`exact_solution_norm_bound_nonauto`
  signature, `joint_lipschitz_pair_bound`, etc.) reproduced as
  hypotheses.

If you submit, save the project ID to
`.prover-state/aristotle_submissions/cycle_066/project_ids.txt` and
include it in the cycle 066 task results. Cycle 067 will check the
result at its start.

**Do not block cycle 066 on this step.** It is purely opportunistic.

---

## Step 5 (mandatory): write task results + commit

Write `.prover-state/task_results/cycle_066.md` per the CLAUDE.md
template. Include:

* Aristotle status from Step 1 (with project ID).
* Which §406D helpers landed.
* Faithfulness check entries for each new `_nonauto` lemma.
* Whether (4)+(5) were deferred to cycle 067 (per the hard line in
  Step 2).
* Aristotle submission ID for cycle 067 if Step 4 ran.

Update `.prover-state/issues/non_autonomous_lift_plan.md` to mark
"Cycle 066 — lift §406D recurrence helpers" as RESOLVED (or
PARTIAL with the deferred items listed if Step 2's hard line
triggered).

Commit message follows the cycle 062–065 pattern:
`Cycle 066 — §406D recurrence cluster non-autonomous lift`.

---

## What NOT to do

* **Do NOT touch the cycle 040–044 autonomous helpers.** They are
  consumed by `stable_consistent_isConvergent_autonomous` (line
  4403). The cycle 066 task is to ADD `_nonauto` variants
  alongside, not to replace them.
* **Do NOT poll Aristotle more than once in cycle 066.** CLAUDE.md
  is explicit on this. One check at Step 1, then proceed.
* **Do NOT attempt to close `stable_consistent_isConvergent`
  (line 4552) this cycle.** It is the cycle 068 target. The cycle
  066+067 lifts must land first.
* **Do NOT raise `maxHeartbeats` above 200000.** Decompose if a proof
  becomes slow.
* **Do NOT introduce `axiom`/`constant`** for any joint-Lipschitz
  reformulation that proves awkward. The cycle 065 joint-Lipschitz
  pattern works; if a §406D helper resists it, file an issue and
  defer that specific helper, not the whole cluster.
* **Do NOT rewrite cycle 065's `residual_bound_nonauto` /
  `deriv_diff_bound_nonauto` proofs.** They are the agreed
  reference shape. If Aristotle returns alternative proofs, only
  swap if the diff is dramatic (≥ 30 % LOC reduction) — see Step 1.
* **Do NOT use `add_le_add_left` for monotone-addition with a left
  constant.** The cycle 065 worker discovered Lean dispatches this
  to a right-add covariant instance, producing type mismatches.
  Use `linarith [hA]` or `gcongr` instead. (Saved in feedback
  memory; see also `.prover-state/task_results/cycle_065.md` §"Dead
  ends".)
* **Do NOT bundle T3_bound's lift with T1/T2.** T3 is a trivial
  wrapper of cycle 065's `localTruncationError_bound_nonauto`; bundling
  hides the trivial nature and clutters the proof structure. Land
  it as its own one-liner.
* **Do NOT try to replace `globalError_decomposition` (line 1094)
  with a new non-autonomous variant.** Inspect first — it likely
  already takes `IsLMMSolution h x₀ f Y` (non-autonomous shape) and
  works as-is for the lift. If it doesn't, the fix is upstream
  in cluster 1, not cluster 2; file an issue.
* **Do NOT modify `scripts/autonomous_loop.py`.** The standing
  prompt-builder bug from `tautology_scanner_false_positives.md`
  is loop-maintainer territory.
* **Do NOT spend time on the "phantom" framing if the cycle 066
  prompt later carries a stale "stuck on" verdict.** Prior phantoms
  (cycles 008/014/015/040) were always `attempts.md` propagation
  bugs. The cycle 066 verification is: `git log -1` shows the cycle
  065 commit `9e5d2ee`; `lake env lean OpenMath/Chapter4/Section404.lean`
  exits 0 with one sorry at line 4552. If both pass, the cycle 065
  work landed; the prompt is wrong.

---

## Cross-references

* `.prover-state/issues/non_autonomous_lift_plan.md` — four-cluster
  roadmap; Cluster 1 (§406B) RESOLVED in cycle 065; cluster 2
  (§406D) is this cycle's target.
* `.prover-state/task_results/cycle_065.md` — cycle 065 deliverable
  record + the `add_le_add_left` discovery.
* `.prover-state/issues/lem_406B_textbook_check.md` — corrected LTE
  bound coefficient; cycle 065's lift inherits this.
* `OpenMath/Chapter4/Section404.lean:1180–1480` — autonomous §406D
  recurrence helpers (T1/T2/T3 + recurrence_bound +
  recurrence_bound_textbook).
* `OpenMath/Chapter4/Section404.lean:4101` — cycle 065's
  `joint_lipschitz_pair_bound` (the joint-Lipschitz triangle
  inequality used in `residual_bound_nonauto` / `deriv_diff_bound_nonauto`).
* `OpenMath/Chapter4/Section404.lean:4129–4413` — cycle 065's §406B
  non-autonomous helpers (the cluster cycle 066 builds on).
* `OpenMath/Chapter4/Section404.lean:4548–4552` — the sorry to close
  in cycle 068 (NOT this cycle).

---

## Quick-reference: cycle 065 helpers cycle 066 builds on

| Helper | Line | Use in cycle 066 |
|---|---|---|
| `joint_lipschitz_pair_bound` | 4101 | T1/T2 Lipschitz step IF time args differ (analysis suggests they don't) |
| `lipschitzInSecond_univ_toLipschitzWith` | 3862 | T1/T2 Lipschitz step when time args coincide (expected default) |
| `LinearMultistepMethod.localTruncationError_bound_nonauto` | 4353 | T3_bound_nonauto body |
| `f_yex_bound_on_Icc` | 3885 | (not needed cluster 2; cluster 4 only) |
| `hstart_shape_bridge` | 3916 | (not needed cluster 2; cluster 4 only) |

Aim for cycle 066 to mirror cycle 065's structure: a tight
~200-LOC commit that lifts one cluster cleanly, with the autonomous
helpers preserved.
