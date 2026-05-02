# Cycle 063 Strategy — Adapter lemmas at the autonomous/non-autonomous boundary

## TL;DR

Cycle 062 (commit `1eaf808`) closed the **autonomous-IVP form** of
Theorem 406D as `LinearMultistepMethod.stable_consistent_isConvergent_autonomous`
at `OpenMath/Chapter4/Section404.lean:3863` — the analytical core.
The remaining single sorry at line 4012 is the **non-autonomous lift**
to the textbook `IsConvergent` predicate (which takes
`f : ℝ → ℝ → ℝ` with `LipschitzInSecond Set.univ L f`, not autonomous
`f : ℝ → ℝ` with `LipschitzWith L.toNNReal f`).

The cycle 062 task results estimate the lift at **200–400 lines of
Lipschitz bookkeeping, no new mathematics**. Realistically that is
**a 4–5 cycle effort**: 19 helpers along the cycle 040–062 chain
take `{f : ℝ → ℝ}` and need non-autonomous variants taking
`{f : ℝ → ℝ → ℝ}`. The cycle 060 regression (score −1) showed that
single-cycle ~430-line targets risk vacuous-proof bugs; cycle 061
and 062 (3 wrappers + 1 wrapper, scores +1 and +2) showed that
small decomposed wins land cleanly.

**Cycle 063 scope:** build the **3 small adapter lemmas** at the
autonomous/non-autonomous boundary, file the multi-cycle refactor
plan, and batch-submit the adapters to Aristotle. **Do NOT** attempt
to refactor the cycle 040–062 helper chain in this cycle. **Do NOT**
attempt to close the line-4012 sorry directly.

---

## Priority 0 — sanity checks before starting

Run these once at the start of the cycle:

```bash
# 1. Branch tip is the cycle 062 commit.
git log -1 --format='%H %s'
# Expected: 1eaf808 Cycle 062 — autonomous-IVP form of thm:406D + aOf_tendsto_zero wrapper

# 2. Section404.lean has exactly one sorry at line 4012.
rg '\bsorry\b' OpenMath/Chapter4/Section404.lean -n
# Expected: a single hit at line 4012.

# 3. The file compiles cleanly (modulo the documented sorry).
lake env lean OpenMath/Chapter4/Section404.lean
# Expected: clean exit, no errors beyond the documented sorry.
```

If a second sorry has crept in, or the branch tip is not `1eaf808`,
stop and triage before proceeding. The "stuck on" framing in the
prompt about line 4012 is **expected** (cycle 062 explicitly left
that sorry as the cycle 063+ target).

---

## Priority 1 — the three adapter lemmas

All three live in `OpenMath/Chapter4/Section404.lean`, placed
**immediately above** the autonomous theorem at line 3863 (so they
sit at the boundary). They are deliberately small and
Aristotle-friendly.

### Adapter 1 — `LipschitzInSecond` to per-`x` `LipschitzWith`

**Why:** the cycle 062 autonomous theorem expects
`LipschitzWith L.toNNReal f` for autonomous `f : ℝ → ℝ`. The
non-autonomous `IsConvergent` predicate gives
`LipschitzInSecond Set.univ L f` for `f : ℝ → ℝ → ℝ`. The bridge is
direct because
`LipschitzInSecond s L f := ∀ x ∈ s, LipschitzWith L (f x)`
(see `OpenMath/Chapter1/Section110.lean:45`), so on `Set.univ` the
universal hypothesis is automatic.

**Statement (place above the autonomous theorem):**

```lean
/-- **Adapter (cycle 063): `LipschitzInSecond Set.univ` ⇒ per-`x`
`LipschitzWith` on the autonomous restriction.**

The non-autonomous `IsConvergent` predicate hypothesises
`LipschitzInSecond Set.univ L f`; the autonomous helper chain
(cycles 040–062) requires `LipschitzWith L (f x)` for each `x`.
This is the trivial unfolding bridge. -/
private lemma lipschitzInSecond_univ_toLipschitzWith
    {L : ℝ≥0} {f : ℝ → ℝ → ℝ}
    (hf_lip : OpenMath.Chapter1.Section110.LipschitzInSecond Set.univ L f)
    (x : ℝ) :
    LipschitzWith L (f x) :=
  hf_lip x (Set.mem_univ _)
```

**Expected proof:** the term `hf_lip x (Set.mem_univ _)` should close
it directly (`LipschitzInSecond` unfolds to `∀ x ∈ s, …`). If Lean
rejects, try `by exact hf_lip x (Set.mem_univ _)` or check the
unfolded shape with `lean_hover_info` on `LipschitzInSecond`.

**Aristotle:** trivial; expect a 1-line solution.

---

### Adapter 2 — `f t (yex t)` is bounded on `[x₀, x]`

**Why:** the autonomous theorem hypothesises
`hf_yex_bound : ∀ t : ℝ, |f (yex t)| ≤ M_bound` (a uniform bound
over all of ℝ). The non-autonomous `IsConvergent` does not directly
hypothesise such a bound. We extract one from compactness: on the
compact interval `[x₀, x]`, the continuous function
`t ↦ |f t (yex t)|` attains a maximum.

**Statement (place above the autonomous theorem):**

```lean
/-- **Adapter (cycle 063): bound for `f t (yex t)` on a compact
interval.**

Given `f : ℝ → ℝ → ℝ` jointly continuous and `yex : ℝ → ℝ`
continuous, the function `t ↦ |f t (yex t)|` is bounded on every
closed interval. The bound is the `M_bound` the autonomous theorem
chain consumes; the cycle 064+ refactor will re-derive the
autonomous helpers to take a compact-restricted bound rather than
the global `∀ t : ℝ` form.

Note: this gives a bound on `Set.Icc (min x₀ x) (max x₀ x)`, NOT on
all of ℝ. The autonomous theorem's `∀ t : ℝ` is stricter than what
continuity alone delivers. The cycle 064+ refactor will adapt the
helper chain to the compact-restricted form. -/
private lemma f_yex_bound_on_Icc
    {f : ℝ → ℝ → ℝ}
    (hf_cont : Continuous (Function.uncurry f))
    {yex : ℝ → ℝ} (hyex_cont : Continuous yex)
    (x₀ x : ℝ) :
    ∃ M_bound : ℝ, 0 ≤ M_bound ∧
      ∀ t ∈ Set.Icc (min x₀ x) (max x₀ x), |f t (yex t)| ≤ M_bound := by
  sorry
```

**Proof sketch:**
- `(fun t => |f t (yex t)|)` is continuous: rewrite as
  `|Function.uncurry f (t, yex t)|`, then compose
  `continuous_id.prod_mk hyex_cont` with `hf_cont` and `continuous_abs`.
- `Set.Icc (min x₀ x) (max x₀ x)` is compact via `isCompact_Icc`,
  and is non-empty since `min x₀ x ≤ max x₀ x`.
- Continuous function on compact non-empty set attains its max:
  `IsCompact.exists_isMaxOn` (verify name with
  `lean_local_search "exists_isMaxOn"`).
- Take `M_bound = |f t₀ (yex t₀)|` for the maximizer `t₀`.

**Manual proof attempt (if Aristotle fails):**

```lean
  have hcont : Continuous (fun t : ℝ => |f t (yex t)|) := by
    have hpair : Continuous (fun t : ℝ => (t, yex t)) :=
      continuous_id.prod_mk hyex_cont
    exact (hf_cont.comp hpair).abs
  have hcpt : IsCompact (Set.Icc (min x₀ x) (max x₀ x)) := isCompact_Icc
  have hnonempty : (Set.Icc (min x₀ x) (max x₀ x)).Nonempty :=
    Set.nonempty_Icc.mpr (min_le_max)
  obtain ⟨t₀, ht₀_mem, ht₀_max⟩ :=
    hcpt.exists_isMaxOn hnonempty hcont.continuousOn
  refine ⟨|f t₀ (yex t₀)|, abs_nonneg _, fun t ht => ?_⟩
  exact ht₀_max ht
```

**Aristotle:** submit; ~25 lines if Aristotle finds the right
compactness lemma. The fallback above is the manual route.

---

### Adapter 3 — starting-data shape bridge

**Why:** the autonomous theorem hypothesises per-`h`
`hstart : ∀ j : Fin k, Tendsto (fun h => yex (x₀ + j·h) − Yh h j)
(nhds 0) (nhds 0)`. The non-autonomous `IsConvergent` uses the
textbook shape `hstart : ∀ i : Fin k, Tendsto (start · i) (nhds 0)
(nhds y₀)`. The two are equivalent under continuity of `yex` at
`x₀` and `yex x₀ = y₀` (which the `IsConvergent` predicate
provides via `HasDerivAt`).

**Statement (place above the autonomous theorem):**

```lean
/-- **Adapter (cycle 063): starting-data shape bridge.**

The non-autonomous `IsConvergent` predicate uses the textbook
starting-data shape `start h i → y₀`; the autonomous theorem (and
the cycle 040–062 helper chain) uses the per-`h` shape
`yex (x₀ + j·h) − Yh h j → 0`. The two are equivalent under
continuity of `yex` at `x₀` and `yex x₀ = y₀` (which the
`IsConvergent` predicate provides via `HasDerivAt`).

This adapter is the boundary lemma that lets cycle 064+ thread
the textbook starting-data hypothesis through the autonomous
helper chain. -/
private lemma hstart_shape_bridge
    {k : ℕ} {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_cont_x₀ : ContinuousAt yex x₀)
    {start : ℝ → Fin k → ℝ}
    (hstart : ∀ i : Fin k,
        Filter.Tendsto (fun h : ℝ => start h i) (nhds 0) (nhds y₀)) :
    ∀ j : Fin k,
      Filter.Tendsto
        (fun h : ℝ => yex (x₀ + (j.val : ℝ) * h) - start h j)
        (nhds 0) (nhds 0) := by
  sorry
```

**Proof sketch:**
- Fix `j : Fin k`. The map `h ↦ x₀ + j·h` is continuous and equals
  `x₀` at `h = 0`, so `h ↦ yex (x₀ + j·h)` tends to `yex x₀ = y₀`
  as `h → 0` (composition + `ContinuousAt`).
- Combined with `start h j → y₀`, the difference tends to
  `y₀ − y₀ = 0` via `Filter.Tendsto.sub`.

**Manual proof attempt:**

```lean
  intro j
  have hlin : Filter.Tendsto (fun h : ℝ => x₀ + (j.val : ℝ) * h)
      (nhds 0) (nhds x₀) := by
    have : Filter.Tendsto (fun h : ℝ => x₀ + (j.val : ℝ) * h)
        (nhds 0) (nhds (x₀ + (j.val : ℝ) * 0)) := by fun_prop
    simpa using this
  have hyex_lim : Filter.Tendsto (fun h : ℝ => yex (x₀ + (j.val : ℝ) * h))
      (nhds 0) (nhds y₀) := by
    have := hyex_cont_x₀.tendsto.comp hlin
    rwa [hyex_x₀] at this
  have hsub := hyex_lim.sub (hstart j)
  simpa using hsub
```

**Aristotle:** submit; ~15 lines.

---

## Priority 2 — issue file documenting the cycle 064+ refactor plan

Create `.prover-state/issues/non_autonomous_lift_plan.md` with the
following exact content (this is the authoritative roadmap for
cycles 064–067):

```markdown
# Issue: Non-autonomous lift of `stable_consistent_isConvergent`

## Status

Cycle 062 closed `LinearMultistepMethod.stable_consistent_isConvergent_autonomous`
(autonomous-IVP form, scalar `f : ℝ → ℝ`) at
`OpenMath/Chapter4/Section404.lean:3863`. The textbook `IsConvergent`
predicate (def:402A, line 305) is non-autonomous (`f : ℝ → ℝ → ℝ`).
The lift to `LinearMultistepMethod.stable_consistent_isConvergent`
(line 4012) requires re-deriving 19 helpers from the cycle 040–062
chain to accept `f : ℝ → ℝ → ℝ` with `LipschitzInSecond Set.univ L f`.

## Cycle 063 deliverables (the boundary adapters)

* `lipschitzInSecond_univ_toLipschitzWith` — converts the
  non-autonomous Lipschitz predicate to the per-`x` autonomous form
  the helper chain consumes.
* `f_yex_bound_on_Icc` — extracts a uniform bound on `[x₀, x]` from
  joint continuity of `f` and continuity of `yex`.
* `hstart_shape_bridge` — bridges the textbook `start h i → y₀`
  shape to the per-`h` `yex (x₀+j·h) − Yh h j → 0` shape.

These three adapters form the autonomous/non-autonomous boundary;
the cycle 064+ refactor builds on them.

## Cycle 064–067 refactor plan (bottom-up)

Each helper currently takes `{f : ℝ → ℝ}` and uses autonomous `f y`
calls. The non-autonomous variant takes `{f : ℝ → ℝ → ℝ}` and uses
`f t y`, with a `LipschitzInSecond` (or per-`x` `LipschitzWith`)
hypothesis. List in dependency order:

### Cycle 064 — lift §406B sub-lemmas (~150 lines)

* `exact_solution_norm_bound` (line 568)
* `residual_integral_form` (line 624)
* `residual_bound` (line 692)
* `deriv_diff_bound` (line 790)
* `localTruncationError_bound` = `lem:406B` (line 923)

### Cycle 065 — lift §406D recurrence helpers (~200 lines)

* `T1_bound` (line 1180)
* `T2_term_bound` (line 1200)
* `globalError_step_bound` (line 1241)
* `globalError_recurrence_form` (line 2544)
* `globalError_recurrence_form_explicit` (line 3249)

### Cycle 066 — lift cycle 057–061 squeeze helpers (~100 lines)

* `globalError_outer_squeeze_a_term`
* `globalError_outer_squeeze_c_term`
* `bOf_tendsto_at_zero`, `cOf_tendsto_at_zero`,
  `aOf_tendsto_zero`, `bOf_limit_pos`

### Cycle 067 — close `stable_consistent_isConvergent` (~80 lines)

Lift `globalError_closed_form_autonomous_explicit` to non-autonomous
and prove `stable_consistent_isConvergent` directly, using:
* the cycle 063 adapters (Lipschitz, bound, hstart bridge);
* the cycle 064–066 lifted helpers.

## Why a refactor cycle by cycle (not one big cycle)

* Cycle 060 (~430 lines, single-cycle target) regressed (score −1)
  because complexity outpaced verification. Cycle 061 (3 wrappers,
  +1) and cycle 062 (autonomous theorem + wrapper, +2) showed that
  small decomposed wins land cleanly.
* The 19 helpers form 4 natural clusters along the dependency
  chain. Each cluster is ~80–200 lines.
* Aristotle batch-submits at each cluster boundary keep the manual
  effort O(50–100 lines per cycle).

## Hypothesis adaptation rules

For each helper:

* `{f : ℝ → ℝ}` → `{f : ℝ → ℝ → ℝ}`.
* `(hf_lip : LipschitzWith L.toNNReal f)` → either
  `(hf_lip : LipschitzInSecond Set.univ L f)` (and use cycle 063's
  `lipschitzInSecond_univ_toLipschitzWith` adapter inside the body)
  or per-`x` `(hf_lip : ∀ x, LipschitzWith L.toNNReal (f x))`.
* `(hyex_ode : ∀ t, deriv yex t = f (yex t))` →
  `(hyex_ode : ∀ t, deriv yex t = f t (yex t))`.
* `(hf_yex_bound : ∀ t, |f (yex t)| ≤ M_bound)` →
  `(hf_yex_bound : ∀ t ∈ Set.Icc x₀ x, |f t (yex t)| ≤ M_bound)`
  (compact-restricted) plus, where the helper indexes off the
  trajectory, the appropriate restriction.
* `(hY : M.IsLMMSolution h x₀ (fun _ y => f y) Y)` →
  `(hY : M.IsLMMSolution h x₀ f Y)`.

## Cross-references

* `extraction/formalization_data/entities/thm_406D.json` — textbook
  statement (non-autonomous).
* `OpenMath/Chapter4/Section404.lean:3863` — autonomous theorem
  (cycle 062).
* `OpenMath/Chapter4/Section404.lean:4012` — the sorry to close
  (cycle 067).
* `.prover-state/task_results/cycle_062.md` — original lift
  estimate (200–400 lines, "no deep new mathematics").
```

---

## Priority 3 — Aristotle batch

Submit the **3 adapter lemmas** to Aristotle as a single submission
(via `mcp__aristotle__submit_file` if creating a single .lean file
with all three, or `mcp__aristotle__submit_prompt` per lemma). Each
is small enough to close in one Aristotle round.

After submission:
1. Sleep **30 minutes** (CLAUDE.md rule, not 5 min, not 60 min).
2. Check **once** with `mcp__aristotle__get_status`.
3. Incorporate any returned proofs (with attribution in docstring).
4. For any adapter Aristotle did not close, fall back to the
   manual proof sketches above.

**Do NOT poll Aristotle more than once after the 30-minute sleep.**

---

## What NOT to do

* **Do NOT** attempt to close the line-4012 sorry in cycle 063. The
  cycle 062 task results estimated 200–400 lines for the full lift,
  which is multi-cycle work. Trying to do it all in one cycle risks
  the cycle 060 regression pattern (score −1).
* **Do NOT** refactor any of the cycle 040–062 autonomous helpers
  to non-autonomous form in cycle 063. That is the cycle 064–067
  scope per the issue file.
* **Do NOT** modify `LinearMultistepMethod.stable_consistent_isConvergent_autonomous`
  (the cycle 062 deliverable at line 3863). It is the analytical
  core; the lift builds on top of it.
* **Do NOT** introduce `axiom` or `constant` declarations.
* **Do NOT** raise `maxHeartbeats` above 200000.
* **Do NOT** treat the line-4012 sorry as a "regression" to fix; it
  was deliberately left in cycle 062 per the strategy and is the
  cycle 067 target.
* **Do NOT** modify `scripts/autonomous_loop.py` (loop-maintainer
  territory; see `tautology_scanner_false_positives.md`).
* **Do NOT** delete or weaken any of the cycle 040–062 helpers as
  a "shortcut". The autonomous chain is load-bearing for cycle 067.
* **Do NOT** write the adapter lemmas as `theorem` or
  non-`private`. They are internal scaffolding for the cycle 064+
  refactor.
* **Do NOT** cherry-pick a different Chapter 4 entity (e.g.
  `thm:410A`, `thm:443A`) instead of cycle 063's adapters. Per
  CLAUDE.md, "Follow the strategy. Do not cherry-pick easy goals."
  The non-autonomous lift of `thm:406D` is the canonical thread to
  pull because it unblocks the textbook form of the marquee
  cycle 040–062 result.

---

## Acceptance criteria for cycle 063

A successful cycle 063 commit produces:

1. **Three new private lemmas** in
   `OpenMath/Chapter4/Section404.lean`, placed immediately above
   line 3863:
   - `lipschitzInSecond_univ_toLipschitzWith`
   - `f_yex_bound_on_Icc`
   - `hstart_shape_bridge`

   All three compile cleanly (no `sorry`, no `axiom`).

2. **One new issue file**:
   `.prover-state/issues/non_autonomous_lift_plan.md` documenting
   the cycle 064–067 refactor plan (use the template in §"Priority 2"
   above verbatim).

3. **Verification**:
   - `lake env lean OpenMath/Chapter4/Section404.lean` exits clean.
   - `rg '\bsorry\b' OpenMath/Chapter4/Section404.lean -n` shows
     exactly 1 hit (the line-4012 main theorem, unchanged).
   - `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`
     returns no new tautology hits.
   - Axiom check on the three new adapters: only
     `[propext, Classical.choice, Quot.sound]`.

4. **`task_results/cycle_063.md`** documenting:
   - Each adapter's statement, proof approach, and Aristotle status.
   - The issue file reference.
   - Cycle 064 next-step (lift the §406B sub-lemmas: see issue file).

5. **Faithfulness check** in the task results:
   - Each adapter is internal scaffolding; not a Butcher-named
     entity. Document accordingly.
   - Adapter 2 introduces a *compact-restricted* bound (weaker than
     the autonomous theorem's `∀ t : ℝ`). The cycle 064+ refactor
     will adapt the helpers to consume the compact-restricted form.
     Document this as a deliberate scope decision in adapter 2's
     docstring.
   - Tautology check: each adapter does real work (not vacuous
     hypothesis re-export).

---

## Faithfulness flags for the worker

* **Adapter 1** is a definitional unfolding bridge — no
  faithfulness divergence. Document in docstring as "trivial
  unfolding bridge".
* **Adapter 2** introduces a *compact-restricted* bound. The
  autonomous theorem's `∀ t : ℝ` is stricter than what continuity
  delivers; the cycle 064+ refactor will re-derive the autonomous
  helpers to consume the compact-restricted form. Document this as
  a deliberate scope decision; not a divergence from the textbook
  (the textbook's `M = max …` is implicitly compact-restricted).
* **Adapter 3** uses `ContinuousAt yex x₀` (extractable from
  `HasDerivAt yex … x₀` in the `IsConvergent` predicate via
  `HasDerivAt.continuousAt`) plus `yex x₀ = y₀`. Both are
  immediate from `IsConvergent`'s hypotheses. No new mathematical
  content.

---

## Strategic context (for the worker's awareness, not action)

The cycle 062 commit `1eaf808` proves the autonomous form, which is
the analytical core. The non-autonomous lift is mechanical
bookkeeping. After cycle 067 closes
`stable_consistent_isConvergent`, the natural follow-ups are
(per `plan.md` Chapter 4):

* `thm:406C` (already done — global error bound for LMMs).
* `thm:243A` (cross-chapter Ch.2→Ch.4 deferral; consumes
  `IsConvergent`).
* `thm:405A`, `thm:405B`, `thm:405C` (necessity-of-conditions
  theorems for convergence; all consume `IsConvergent`
  symbolically).

None of these are blocked by cycle 063's scope; cycle 063 is purely
the entry point for the cycle 067 closure of `thm:406D`'s textbook
form. The worker should focus on cycle 063's three adapters and the
issue file, not on these downstream targets.
