# Cycle 067 Strategy — `globalError_per_step_sum_form` and `globalError_recurrence_form_explicit` non-autonomous lift

## TL;DR

Cluster 3 of the cycle 064–069 four-cluster non-autonomous lift plan.
Cycle 066 closed cluster 2 (six §406D recurrence helpers) at score
+1. The remaining sorry is `stable_consistent_isConvergent` at
`OpenMath/Chapter4/Section404.lean:4928`.

The cycle 064 plan in
`.prover-state/issues/non_autonomous_lift_plan.md` lists cluster 3
as "lift the cycle 057–061 squeeze helpers". Re-reading the source
(see analysis below) shows that those named squeeze helpers
(`globalError_outer_squeeze_a_term`, `globalError_outer_squeeze_c_term`,
`bOf_tendsto_at_zero`, `cOf_tendsto_at_zero`, `aOf_tendsto_zero`,
`bOf_limit_pos`) are **already shape-agnostic** — they take
`{a b c : ℝ → ℝ}` or scalar `Θ L M_bound` and consume no `f`-shape
data. They will be reused directly by the cycle 068 closure.

The actual cluster-3 lift work is to lift the two intermediate
helpers that *do* take an autonomous `f : ℝ → ℝ`:

1. `globalError_per_step_sum_form` (line 2542, ~50-line body) — a
   thin wrapper around cycle 045's `globalError_recurrence_bound_textbook`.
2. `globalError_recurrence_form_explicit` (line 3249, ~430-line body)
   — the heavy assembly that bundles the per-step sum bound, the
   `theta`-decomposition, and the `recentSum_swap_bound` index
   arithmetic into the `aOf, bOf, cOf` recurrence shape.

Both lifts are **mechanical 1:1 ports** under the cycle 065
joint-Lipschitz hypothesis form. No new mathematics is involved.
The §406B/§406D sub-lemmas they consume are already lifted (cycle
064–066).

This cycle's ceiling is **~500 LOC**. If you hit ~300 LOC and the
`_explicit_nonauto` body is not done, snapshot and defer the rest to
cycle 068; do **not** push past 500 LOC.

---

## Step 0 (≤ 5 minutes) — Aristotle status check

Run `mcp__aristotle__get_status` once on project
`55543850-b9f1-4dab-9d34-e65f732f030c` (cycle 065's submission for
alternative proofs of `residual_bound_nonauto` and
`deriv_diff_bound_nonauto`).

* If the status is `IN_PROGRESS` and progress is below ~50%,
  treat the submission as not contributing. The cycle 065 manual
  proofs are clean (`L_joint · (1 + M_bound)` shape) and already
  consumed by cycle 066's recurrence cluster, so any returning
  Aristotle proof would be redundant. Move on.
* If the submission has *completed*, you may extract proofs for
  reference, but do **not** swap them in. The cycle 065 manual
  proofs have been validated by the cycle 066 build; replacing them
  is unnecessary churn.
* CLAUDE.md cadence rule: poll **once**, not repeatedly.

---

## Step 1 — Lift `globalError_per_step_sum_form` to non-autonomous

**Target**: insert immediately after
`LinearMultistepMethod.globalError_recurrence_bound_textbook_nonauto`
(line 4644, end of cycle 066 cluster), as a new `private lemma`.

### Statement

```lean
private lemma globalError_per_step_sum_form_nonauto
    {k : ℕ} (M : LinearMultistepMethod k) (hcons : M.IsConsistent)
    {f : ℝ → ℝ → ℝ} {L_joint M_bound : ℝ}
    (hL_joint : 0 ≤ L_joint) (hM : 0 ≤ M_bound)
    (hf_lip_joint : LipschitzWith L_joint.toNNReal (Function.uncurry f))
    {yex : ℝ → ℝ}
    (hyex_C1 : ContDiff ℝ 1 yex)
    (hyex_ode : ∀ t, deriv yex t = f t (yex t))
    (hf_yex_bound : ∀ t, |f t (yex t)| ≤ M_bound)
    {Y : ℕ → ℝ} {x₀ h : ℝ}
    (hh : 0 ≤ h)
    (hsmall : h * L_joint * |M.β 0| < 1)
    (hY : M.IsLMMSolution h x₀ f Y)
    (n : ℕ) (hn : k ≤ n) :
    |yex (x₀ + (n : ℝ) * h) - Y n
        - ∑ i : Fin k, M.α i.succ
            * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                - Y (n - (i.val + 1)))|
      ≤ (h * L_joint * (|M.β 0| * (∑ i : Fin k, |M.α i.succ|)
                  + ∑ i : Fin k, |M.β i.succ|)
            / (1 - h * L_joint * |M.β 0|))
          * (∑ j : Fin k,
              |yex (x₀ + ((n - (j.val + 1) : ℕ) : ℝ) * h)
                - Y (n - (j.val + 1))|)
        + ((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
            + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
              * L_joint * (1 + M_bound) * h^2
            / (1 - h * L_joint * |M.β 0|) := by
  -- Specialise `Mmax` to the sum of recent errors.
  set Mmax : ℝ :=
    ∑ j : Fin k,
      |yex (x₀ + ((n - (j.val + 1) : ℕ) : ℝ) * h)
        - Y (n - (j.val + 1))|
  have hMmax_nn : 0 ≤ Mmax :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hMmax_bound :
      ∀ i : Fin k,
        |yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
          - Y (n - (i.val + 1))| ≤ Mmax := by
    intro i
    exact Finset.single_le_sum
            (f := fun j : Fin k =>
              |yex (x₀ + ((n - (j.val + 1) : ℕ) : ℝ) * h)
                - Y (n - (j.val + 1))|)
            (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  exact M.globalError_recurrence_bound_textbook_nonauto hcons hL_joint hM
          hf_lip_joint hyex_C1 hyex_ode hf_yex_bound hh hsmall hY n hn
          Mmax hMmax_nn hMmax_bound
```

### Key differences from autonomous source (line 2542)

| Autonomous | Non-autonomous |
| --- | --- |
| `{f : ℝ → ℝ}` | `{f : ℝ → ℝ → ℝ}` |
| `hL : 0 ≤ L` | `hL_joint : 0 ≤ L_joint` |
| `hf_lip : LipschitzWith L.toNNReal f` | `hf_lip_joint : LipschitzWith L_joint.toNNReal (Function.uncurry f)` |
| `hyex_ode : ∀ t, deriv yex t = f (yex t)` | `hyex_ode : ∀ t, deriv yex t = f t (yex t)` |
| `hf_yex_bound : ∀ t, \|f (yex t)\| ≤ M_bound` | `hf_yex_bound : ∀ t, \|f t (yex t)\| ≤ M_bound` |
| `hY : M.IsLMMSolution h x₀ (fun _ y => f y) Y` | `hY : M.IsLMMSolution h x₀ f Y` |
| Bound coeff `L * M_bound * h^2` | Bound coeff `L_joint * (1 + M_bound) * h^2` |
| Calls `globalError_recurrence_bound_textbook` | Calls `globalError_recurrence_bound_textbook_nonauto` |

### Verify

```bash
lake env lean OpenMath/Chapter4/Section404.lean
```

Should exit 0. The single sorry at line 4928 remains.

### Estimated effort

~50 LOC including docstring. The proof body is the autonomous body
verbatim modulo the closing lemma name. **This is the easy half of
the cycle. Aim to land it in the first 30 minutes.**

---

## Step 2 — Lift `globalError_recurrence_form_explicit` to non-autonomous

**Target**: insert immediately after `globalError_per_step_sum_form_nonauto`,
as a new `private lemma`. **DO NOT** modify the autonomous version
(the cycle 062 closure
`stable_consistent_isConvergent_autonomous` still consumes it).

### Statement

```lean
open OpenMath.Chapter1.Section141 in
private lemma globalError_recurrence_form_explicit_nonauto
    {k : ℕ} (hk : 0 < k) (M : LinearMultistepMethod k)
    (hcons : M.IsConsistent)
    {f : ℝ → ℝ → ℝ} {L_joint M_bound : ℝ}
    (hL_joint : 0 ≤ L_joint) (hM : 0 ≤ M_bound)
    (hf_lip_joint : LipschitzWith L_joint.toNNReal (Function.uncurry f))
    {yex : ℝ → ℝ}
    (hyex_C1 : ContDiff ℝ 1 yex)
    (hyex_ode : ∀ t, deriv yex t = f t (yex t))
    (hf_yex_bound : ∀ t, |f t (yex t)| ≤ M_bound)
    {Y : ℕ → ℝ} {x₀ h : ℝ}
    (hh : 0 ≤ h)
    (hsmall : h * L_joint * |M.β 0| < 1)
    (hY : M.IsLMMSolution h x₀ f Y)
    (Θ : ℝ) (hΘ_nn : 0 ≤ Θ)
    (hΘ : ∀ n, |theta k (fun i : Fin k => M.α i.succ) n| ≤ Θ) :
    0 ≤ aOf M Θ L_joint h yex Y x₀ ∧
    0 < bOf M Θ L_joint h ∧
    0 ≤ cOf M Θ L_joint (1 + M_bound) h ∧
    (∀ n : ℕ, 1 ≤ n →
      |yex (x₀ + (n : ℝ) * h) - Y n|
        ≤ aOf M Θ L_joint h yex Y x₀
          + bOf M Θ L_joint h * h * (k : ℝ) *
              (∑ p ∈ Finset.Ico 1 n,
                |yex (x₀ + (p : ℝ) * h) - Y p|)
          + cOf M Θ L_joint (1 + M_bound) h * h^2 * (n : ℝ)) ∧
    |yex x₀ - Y 0| ≤ aOf M Θ L_joint h yex Y x₀
```

### Method: mechanical port of lines 3249–3683

**Copy the autonomous body verbatim** (lines 3274–3683, ~410 lines)
and apply the following **eight global substitutions**:

1. `hL` → `hL_joint`
2. `hf_lip` → `hf_lip_joint`
3. `(fun _ y => f y)` → `f` (in the `IsLMMSolution` shape inside `hY`)
4. **At the call to `globalError_per_step_sum_form` (autonomous line
   3446)**: replace
   ```lean
   have h_per := globalError_per_step_sum_form M hcons hL hM hf_lip
                   hyex_C1 hyex_ode hf_yex_bound hh hsmall hY i hki
   ```
   with
   ```lean
   have h_per := globalError_per_step_sum_form_nonauto M hcons hL_joint hM
                   hf_lip_joint hyex_C1 hyex_ode hf_yex_bound hh hsmall hY i hki
   ```
5. **`Cbase` definition (autonomous line 3283)**: substitute `L`
   with `L_joint`. Result:
   ```lean
   set Cbase : ℝ := L_joint * (|M.β 0| * (∑ i : Fin k, |M.α i.succ|)
                         + ∑ i : Fin k, |M.β i.succ|)
                       / (1 - h * L_joint * |M.β 0|) with hCbase_def
   ```
6. **`Dbase` definition (autonomous line 3286)**: substitute
   `L * M_bound` with `L_joint * (1 + M_bound)`:
   ```lean
   set Dbase : ℝ := ((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
                     + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
                     * L_joint * (1 + M_bound)
                     / (1 - h * L_joint * |M.β 0|) with hDbase_def
   ```
7. **`hDbase_nn` proof (autonomous line 3296–3304)**: replace `hM`
   with `(by linarith : (0:ℝ) ≤ 1 + M_bound)` in the
   `mul_nonneg` argument.
8. **`h_RHS_eq` rewrite inside `h_psi_bound` (autonomous lines
   3449–3464)**: substitute `L * M_bound` with `L_joint * (1 + M_bound)`
   on both sides. The `ring` close at line 3465 will still go through.

Everything else — `theta_bounded_of_isStable` is not called in this
lemma (it's called by the *caller* `globalError_closed_form_autonomous_explicit`
at line 3720; this lemma already takes `Θ` as a parameter), so no Θ
infrastructure changes; `globalError_closed_form M` (line 3352 call)
is shape-agnostic; `sum_theta_psi_contraction` (line 3487) is
shape-agnostic; `recentSum_swap_bound` (line 3502) is shape-agnostic.

### What stays the same

* All `theta`, `yPrime`, `linRec` infrastructure from
  `OpenMath/Chapter1/Section141.lean`.
* `globalError_eq_linRec` and `globalError_closed_form`
  (autonomous lines 2615, 2668) are pure algebraic identities
  with no `f`-dependence; reuse them directly.
* `sum_theta_psi_contraction`, `recentSum_swap_bound` — no `f`-shape.
* `aOf`, `bOf`, `cOf` definitions — these are functions of
  `Θ, L, h` (and `M_bound, yex, Y, x₀` for some), not of `f` itself.
  Pass `L_joint` where you'd pass `L`, and pass `(1 + M_bound)`
  where you'd pass `M_bound`.
* The case split `n < k` vs `n ≥ k`, and all `linarith`/`nlinarith`
  closes — go through verbatim.

### Verify

```bash
lake env lean OpenMath/Chapter4/Section404.lean
```

Should exit 0. The single sorry at line 4928 remains.

### Estimated effort

~430 LOC (mechanical copy with 8 substitutions). This is the
**heavy half** of the cycle.

### Budget watch — ABORT TO CYCLE 068 IF YOU HIT 500 LOC

Cycle 060 (score −1) demonstrated that single-cycle 430-LOC pushes
are fragile. If at any point the cycle's total LOC delta exceeds
**500**, OR if Step 2 has not produced a clean
`lake env lean` build by the time you reach 500 LOC, **stop**:

1. Snapshot whatever lines 3274–3683 you've already ported into
   `globalError_recurrence_form_explicit_nonauto`. Leave the
   incomplete proof body as `sorry` at the end (so the file still
   compiles).
2. Update the issue plan
   (`.prover-state/issues/non_autonomous_lift_plan.md`) with a
   "cluster 3 partial completion — Step 1 done, Step 2 deferred to
   cycle 068" note.
3. Commit the partial progress + Step 1.
4. Write `cycle_067.md` documenting the partial completion.

---

## Step 3 — Pre-commit faithfulness check (MANDATORY)

For each new lemma:

### `globalError_per_step_sum_form_nonauto`

* **Entity ID**: not a Butcher entity; intermediate helper for §406D.
  No textbook quote required, but the `M_bound ↦ (1 + M_bound)`
  semantic shift carried over from cycle 065 should be flagged in
  the docstring.
* **Tautology check**: bound, not a hypothesis. ✓
* **Identity check**: trivial wrapper of cycle 066's
  `globalError_recurrence_bound_textbook_nonauto`. The
  "specialise `Mmax`" reduction is real work (not just an `exact`).
  ✓
* **Hypothesis strength**: matches cycle 066. Joint-Lipschitz is
  the natural non-autonomous analogue of cycle 045's per-`x`
  `LipschitzWith`.

### `globalError_recurrence_form_explicit_nonauto`

* **Entity ID**: not a Butcher entity; analytical assembly for
  `thm:406D` (Butcher §406D, p. 347).
* **Tautology check**: bound, not a hypothesis. ✓
* **Identity check**: substantive — bundles
  `globalError_closed_form` (closed-form decomposition),
  `sum_theta_psi_contraction` (Θ-bound), and
  `recentSum_swap_bound` (index swap) into the
  `aOf, bOf, cOf` recurrence shape needed by
  `discrete_gronwall_exp_bound`.
* **Hypothesis strength**: same as autonomous version, with
  `L ↦ L_joint` and `M_bound ↦ (1 + M_bound)`. Joint-Lipschitz is
  the natural non-autonomous analogue.
* **Absent theorem check**: the cycle 068 `stable_consistent_isConvergent`
  closure is not promised inline; only as a strategy commitment. ✓

---

## Step 4 — Commit and update plan

### Update `non_autonomous_lift_plan.md`

Mark cluster 3 as RESOLVED (or PARTIAL if Step 2 was deferred):

```markdown
### Cycle 067 — lift cycle 057–061 squeeze helpers (~100 lines)

* **Re-scoped on cycle 067**: the named squeeze helpers
  (`globalError_outer_squeeze_a_term`, etc.) are already
  shape-agnostic (take `{a b c : ℝ → ℝ}` directly). The actual
  cluster-3 lift work is to lift `globalError_per_step_sum_form`
  and `globalError_recurrence_form_explicit`, which take
  autonomous `f : ℝ → ℝ`.
* `globalError_per_step_sum_form` — **LANDED cycle 067** as
  `globalError_per_step_sum_form_nonauto` (~50 LOC).
* `globalError_recurrence_form_explicit` — **LANDED cycle 067** as
  `globalError_recurrence_form_explicit_nonauto` (~430 LOC,
  mechanical port).

**RESOLVED in cycle 067**: cluster 3 is complete.
```

### Update `task_results/cycle_067.md`

Use the standard cycle template (worked on, approach, result,
faithfulness check, dead ends, discovery, suggested next approach).
Highlight:

* The re-scoping (named squeeze helpers were already shape-agnostic).
* The two new lemmas and their statements.
* Final LOC count.
* Aristotle status from Step 0.

### Commit message template

```
Cycle 067 — §406D recurrence-form non-autonomous lift

`globalError_per_step_sum_form_nonauto` (joint-Lipschitz wrapper of
cycle 066's `_recurrence_bound_textbook_nonauto`) and
`globalError_recurrence_form_explicit_nonauto` (mechanical 1:1 port
of the autonomous assembly under `L ↦ L_joint`,
`M_bound ↦ (1 + M_bound)` substitution). Build clean; sorry count
unchanged (single sorry at line 4928, cycle 068 target).

Cluster 3 of the cycle 064–069 four-cluster non-autonomous lift
plan; see .prover-state/issues/non_autonomous_lift_plan.md.
```

Then `git push` to land the cycle.

---

## What NOT to do

(Carried forward from prior consultant notes and cycle history;
read these before starting.)

### Specifically forbidden this cycle

1. **Do NOT modify the autonomous helpers** at lines 2542–3683.
   The cycle 062 closure `stable_consistent_isConvergent_autonomous`
   still consumes them. Add `_nonauto` parallel versions only.
2. **Do NOT define new `aOf_nonauto`, `bOf_nonauto`, `cOf_nonauto`
   functions.** The existing `aOf, bOf, cOf` are already
   parametrised by scalar `Θ L M_bound`; pass `L_joint` and
   `(1 + M_bound)` to them in the `_nonauto` lemma. A new
   parallel definition would inflate the cycle past budget for no
   semantic gain.
3. **Do NOT raise `maxHeartbeats`** above 200000. The autonomous
   `_explicit` body compiles within budget; the `_nonauto` mirror
   should too. If you hit a heartbeat limit, decompose into smaller
   private lemmas (the autonomous chain already does this) — do
   not raise the limit.
4. **Do NOT introduce `axiom`/`constant`** to bypass any step.
5. **Do NOT poll Aristotle more than once.** CLAUDE.md cadence
   rule (cycle 040 consultant note §C). One status check at the
   start of the cycle is sufficient.
6. **Do NOT attempt to close `stable_consistent_isConvergent`
   itself this cycle.** That is the cycle 068 (or cycle 069 if
   Step 2 deferred) deliverable. Do **not** reach for the cycle
   068 close, even if budget allows; the squeeze-assembly side of
   the close needs its own dedicated cycle to verify
   joint-Lipschitz threading through the per-`m` Tendsto facts.
7. **Do NOT attempt path (b)** ("inline closed-form Grönwall
   closure") from the cycle 066 task results. Path (a) — the
   `_explicit_nonauto` lift — is the plan, since (i) the squeeze
   helpers are already in place, (ii) cycle 068 needs an
   `aOf, bOf, cOf` recurrence shape to consume them, and
   (iii) inlining duplicates work that path (a) does cleanly.
8. **Do NOT lift the named squeeze helpers**
   (`globalError_outer_squeeze_a_term`,
   `globalError_outer_squeeze_c_term`, `bOf_tendsto_at_zero`,
   `cOf_tendsto_at_zero`, `aOf_tendsto_zero`, `bOf_limit_pos`).
   They are already shape-agnostic; cycle 068 reuses them
   verbatim. The cycle 064 plan that listed them as cluster 3 was
   over-conservative; the cycle 066 task results already noted
   this.

### Carried-forward false-positive verdicts (ignore if mentioned in prompt)

The supervisor's prompt-builder occasionally surfaces stale
"commits not reaching repo" / "stuck on previous sorry" verdicts
from `attempts.md`. Per the cycle 008/014/015/040 consultant
analyses (`.prover-state/issues/consultant_advice_cycle_*.md`),
these are typically false positives. Verify the actual git state
with:

```bash
git log -1 --format='%H %s'
git rev-parse HEAD
git rev-parse origin/Main/Experiments
```

If `HEAD == origin/Main/Experiments` and `git diff HEAD~1 HEAD`
is non-empty, the prior cycle landed; ignore the phantom and
proceed with the actual work.

### Deferred to cycle 068

* Closing `stable_consistent_isConvergent` at line 4928. The cycle
  068 strategy will use cycle 067's `globalError_recurrence_form_explicit_nonauto`
  + the existing shape-agnostic squeeze helpers + a joint-Lipschitz
  adapter (TBD: derive joint-Lipschitz on `Function.uncurry f` from
  `LipschitzInSecond Set.univ L f` + continuity, since
  `LipschitzInSecond` is spatial-only). The cycle 063 adapter set
  may need one more entry; cycle 068's strategy will determine
  whether to add it.

### Deferred to cycle 069 (only if Step 2 deferred this cycle)

If cycle 067 Step 2 is deferred, cycle 068 finishes the
`_explicit_nonauto` port and cycle 069 closes
`stable_consistent_isConvergent`.

---

## Reference: prior cycle history (don't repeat)

* **Cycle 060**: −1 score; pushed ~430 LOC in a single cycle and
  regressed. The lesson: 430 LOC ports are fragile; budget-watch
  aggressively.
* **Cycle 062**: +2 score; closed the autonomous-IVP form of
  `thm:406D` in ~150 LOC. Demonstrated that small, well-decomposed
  pushes succeed.
* **Cycle 063**: +1 score; landed three boundary adapters at the
  autonomous/non-autonomous interface. The current cycle 067 work
  builds on these (specifically `lipschitzInSecond_univ_toLipschitzWith`
  for cycle 068's adapter — not used in this cycle but worth
  knowing about).
* **Cycle 064**: +1 score; landed cluster 1 sub-lemmas A and B
  (no Lipschitz invocation, 1:1 lift).
* **Cycle 065**: 0 score; off-strategy but delivered cluster 1
  sub-lemmas C/D + main + α/β-sum wrappers. The
  `M_bound ↦ (1 + M_bound)` shape emerged from the joint-Lipschitz
  hypothesis here; cycle 067's ports inherit it.
* **Cycle 066**: +1 score; landed cluster 2 (six recurrence
  helpers) within budget. The cycle 067 lift consumes
  `globalError_recurrence_bound_textbook_nonauto` directly.

---

## Reference: relevant Mathlib lemmas

None new — Step 1 is a `Finset.single_le_sum` + delegation to
cycle 066's lemma, and Step 2 is a copy of an existing autonomous
proof. All Mathlib infrastructure (`abs_add_le`,
`Finset.abs_sum_le_sum_abs`, `mul_le_mul_of_nonneg_left`, `linarith`,
`nlinarith`, `ring`, `Finset.sum_Ico_succ_top`, `theta_zero`, `Nat.sub_self`)
is already in place from prior cycles.

---

## Estimated total effort

* Step 0: ≤ 5 minutes (Aristotle check).
* Step 1: ≤ 30 minutes (~50 LOC, mechanical).
* Step 2: 60–90 minutes (~430 LOC, mechanical with 8 substitutions).
* Step 3 + Step 4: 15 minutes (faithfulness + plan + commit).

Total: 2–3 hours of focused worker time. Land the commit before
the cycle's session deadline; if Step 2 starts blowing up, snapshot
at 500 LOC and defer.
