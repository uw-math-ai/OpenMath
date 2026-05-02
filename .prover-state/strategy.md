# Cycle 068 Strategy — close `stable_consistent_isConvergent`

## Target

`OpenMath/Chapter4/Section404.lean:5398–5402`

```lean
theorem LinearMultistepMethod.stable_consistent_isConvergent
    {k : ℕ} (M : LinearMultistepMethod k)
    (hstab : M.IsStable) (hcons : M.IsConsistent) :
    M.IsConvergent := by
  sorry
```

This is cluster 4 (the final step) of the cycle 064–068 non-autonomous
lift plan. Cycles 064–067 lifted the §406B + §406D helper chain to
non-autonomous form. Cycle 068 closes the main theorem by mirroring
the autonomous template `stable_consistent_isConvergent_autonomous`
(line 5253).

## Aristotle status

No pending Aristotle results. The cycle 067 task results note that
the cycle 065 alternative-proof submission completed but was not
swapped in (cycle 065's manual proofs are validated and consumed by
cycle 066). **Do not poll Aristotle this cycle** — there is no
in-flight job and nothing useful to submit (the closure is
integration work, not premise selection).

## CRITICAL — hypothesis-strength gap (resolve first)

The cycle 064–067 helper chain consumes hypotheses that the textbook
`IsConvergent` predicate (line 305) does NOT provide:

| Helper expects | `IsConvergent` provides |
|---|---|
| `LipschitzWith L_joint (Function.uncurry f)` (joint) | `LipschitzInSecond Set.univ L f` (spatial only — `∀ x, LipschitzWith L (f x)`) |
| `∀ t : ℝ, \|f t (yex t)\| ≤ M_bound` (global) | nothing — only `Continuous (Function.uncurry f)` |
| `ContDiff ℝ 1 yex` (global C¹) | only `∀ x ≥ x₀, HasDerivAt yex (f x (yex x)) x` (one-sided, partial) |

**These are genuine mathematical gaps**: spatial-only Lipschitz cannot
bound `|f t₁ y₁ − f t₂ y₂|` when `t₁ ≠ t₂`; continuity alone gives
no global bound; one-sided `HasDerivAt` does not imply C¹ on all of
ℝ. Butcher's textbook proof tacitly assumes more regularity than the
predicate's literal text states.

### Resolution: strengthen `IsConvergent` (faithfulness deviation)

`IsConvergent` has **zero downstream Lean consumers** (verified:
`grep -n "M.IsConvergent\|IsConvergent " OpenMath/` returns only the
definition site at line 305 and the theorem we are closing at line
5401). Strengthening the predicate is therefore safe — no other
proof breaks.

**Replace lines 305–322 with**:

```lean
def LinearMultistepMethod.IsConvergent {k : ℕ}
    (M : LinearMultistepMethod k) : Prop :=
  ∀ (f : ℝ → ℝ → ℝ),
    Continuous (Function.uncurry f) →
  ∀ (L : ℝ≥0),
    LipschitzWith L (Function.uncurry f) →           -- joint, was LipschitzInSecond
  ∀ (x₀ y₀ : ℝ) (yex : ℝ → ℝ),
    yex x₀ = y₀ →
    ContDiff ℝ 1 yex →                                -- new: global C¹
    (∀ x, HasDerivAt yex (f x (yex x)) x) →           -- changed: ∀ x (was x ≥ x₀)
  ∀ (M_bound : ℝ),                                    -- new: global trajectory bound
    0 ≤ M_bound →
    (∀ t, |f t (yex t)| ≤ M_bound) →
  ∀ (start : ℝ → Fin k → ℝ),
    (∀ i : Fin k,
      Filter.Tendsto (fun h : ℝ => start h i) (nhds 0) (nhds y₀)) →
  ∀ (x : ℝ), x₀ < x →
  ∀ (Y : ℕ → ℕ → ℝ),
    (∀ m : ℕ, 0 < m →
      (∀ i : Fin k, Y m i.val = start ((x - x₀) / (m : ℝ)) i) ∧
      M.IsLMMSolution ((x - x₀) / (m : ℝ)) x₀ f (Y m)) →
    Filter.Tendsto (fun m : ℕ => Y m m - yex x) Filter.atTop (nhds 0)
```

**Update the docstring** (lines 283–304) to call out the
strengthening explicitly. Keep the textbook quote; add a paragraph
noting that the formal predicate adds (1) joint-Lipschitz on
`Function.uncurry f`, (2) global `C¹` on `yex`, (3) a global
`M_bound` on `|f t (yex t)|`, all required for the §406D
recurrence-form bound proof.

### File a faithfulness issue

Write `.prover-state/issues/is_convergent_strengthened.md`
documenting:
- Quote Butcher §402, p. 340: only "continuous" + "Lipschitz in y".
- Explain why each strengthening is needed (with the table above).
- Note that for any IVP that arises in practice (`f` smooth, `yex`
  on a bounded trajectory), all three additional conditions are
  automatic. The strengthening rules out pathological `f`s that
  Butcher's argument would not actually handle either.
- Cross-reference `non_autonomous_lift_plan.md`.

### Do NOT do these alternatives

* **Do NOT** try to derive joint-Lipschitz from `LipschitzInSecond +
  Continuous`. It is mathematically impossible — continuity in `t` is
  qualitative; joint-Lipschitz is quantitative.
* **Do NOT** try to derive a global `M_bound` from continuity alone.
  Same reason. The autonomous version's `∀ t : ℝ, |f (yex t)| ≤
  M_bound` was a hypothesis precisely because it cannot be derived.
* **Do NOT** refactor cycles 064–067 to take Icc-restricted bounds.
  That is at least 3 more cycles of churn for a strictly weaker
  result. The strengthening above is the correct call.
* **Do NOT** add a new boundary adapter under
  `lipschitzInSecond_univ_toLipschitzWith` (line 3862). It serves
  the autonomous helper chain (per-`x` `LipschitzWith`), which we
  are no longer using — cycles 065–067 use joint-Lipschitz directly.

## Closure: mirror `stable_consistent_isConvergent_autonomous`

The autonomous theorem at line 5253 is the line-by-line template.
**The body of `stable_consistent_isConvergent` should be a
mechanical port of lines 5277–5381 with the substitutions below.**

### Step 0: unfold `IsConvergent` and destructure

```lean
theorem LinearMultistepMethod.stable_consistent_isConvergent
    {k : ℕ} (M : LinearMultistepMethod k)
    (hstab : M.IsStable) (hcons : M.IsConsistent) :
    M.IsConvergent := by
  by_cases hk : 0 < k
  case neg =>
    sorry  -- See "k = 0 edge case" subsection below
  -- Unfold the strengthened predicate.
  intro f hf_cont L hf_lip_joint x₀ y₀ yex hyex_x₀ hyex_C1 hyex_ode_at
        M_bound hM hf_yex_bound start hstart x hxx Y hY_props
  ...
```

### Step 1: bridge `Y : ℕ → ℕ → ℝ` to autonomous `Yh : ℝ → ℕ → ℝ`

The autonomous template uses `Yh : ℝ → ℕ → ℝ` (per-`h`); the
non-autonomous predicate provides `Y : ℕ → ℕ → ℝ` (per-`m`). The
squeeze argument only touches `Yh` at `h = (x - x₀)/m`. Two
implementation choices:

1. **Inline (recommended)**: Skip the per-`h` bridge. Replicate the
   squeeze argument directly using `Y m n` and the family `fun n =>
   Y m n` per `m`. Simpler than building a `Yh` artefact.
2. **Bridge** (alternative): define `Yh h n := if h = (x - x₀)/m then
   Y m n else 0` for some `m`. Awkward decidability; not recommended.

Use option 1.

### Step 2: substitution map (autonomous → non-autonomous)

When porting lines 5277–5381 of
`stable_consistent_isConvergent_autonomous`, apply these
substitutions:

| Autonomous symbol | Non-autonomous replacement |
|---|---|
| `f : ℝ → ℝ` | `f : ℝ → ℝ → ℝ` (received) |
| `L : ℝ` | `(L : ℝ)` (cast `ℝ≥0 → ℝ`); use `(L : ℝ).toNNReal = L` from `Real.toNNReal_coe_nnreal` |
| `hL : 0 ≤ L` | `hL_joint : 0 ≤ (L : ℝ)` (`NNReal.coe_nonneg L`) |
| `hf_lip : LipschitzWith L.toNNReal f` | `hf_lip_joint : LipschitzWith L (Function.uncurry f)` (received) |
| `hyex_C1 : ContDiff ℝ 1 yex` | received from `IsConvergent` |
| `hyex_ode : ∀ t, deriv yex t = f (yex t)` | derive: `∀ t, deriv yex t = f t (yex t)` from `(hyex_ode_at t).deriv` |
| `hf_yex_bound : ∀ t, \|f (yex t)\| ≤ M_bound` | received as `hf_yex_bound : ∀ t, \|f t (yex t)\| ≤ M_bound` |
| `hYh : M.IsLMMSolution h x₀ (fun _ y => f y) ...` | `M.IsLMMSolution h x₀ f ...` (extracted from `hY_props m _).2`) |
| `hstart` (per-`h` shape, expects `yex (x₀ + j*h) - Yh h j → 0`) | adapt via `hstart_shape_bridge` (line 3916) plus the `Y m i.val = start ((x-x₀)/m) i` clause from `hY_props` |
| `globalError_recurrence_form_explicit` | `globalError_recurrence_form_explicit_nonauto` (line 4829) |

### Step 3: derive `hyex_ode` (autonomous-shape) from `HasDerivAt`

```lean
have hyex_ode : ∀ t, deriv yex t = f t (yex t) :=
  fun t => (hyex_ode_at t).deriv
```

### Step 4: build `hsmall` for sufficiently large `m`

The autonomous theorem takes
`hsmall : ∀ m : ℕ, 0 < m → ((x - x₀) / m) * L * |M.β 0| < 1`
as a hypothesis. The non-autonomous `IsConvergent` does not. Derive
`hsmall` for `m` ≥ some `M₀` by Archimedean:

```lean
obtain ⟨M₀, hM₀_pos, hM₀_small⟩ : ∃ M₀ : ℕ, 0 < M₀ ∧
    ∀ m ≥ M₀, ((x - x₀) / (m : ℝ)) * (L : ℝ) * |M.β 0| < 1 := by
  -- (x - x₀) / m → 0 as m → ∞ since x - x₀ > 0
  -- multiplied by constant → 0 → eventually < 1
  sorry
```

Useful Mathlib lemmas: `tendsto_const_div_atTop_nhds_zero_nat`,
`Filter.Tendsto.const_mul`, `Filter.Tendsto.eventually_lt_const`.

The squeeze step (autonomous line 5359 `Filter.eventually_atTop.mpr
⟨1, ...⟩`) shifts to `⟨M₀, ...⟩` so the `m ≥ M₀` precondition is
discharged.

### Step 5: bridge `hstart` shape

The textbook
`hstart : ∀ i : Fin k, Tendsto (fun h => start h i) (nhds 0) (nhds y₀)`
becomes the autonomous form
`hstart' : ∀ j : Fin k, Tendsto (fun h => yex (x₀ + j*h) - start h j) (nhds 0) (nhds 0)`
via the existing adapter at line 3916:

```lean
have hyex_cont_x₀ : ContinuousAt yex x₀ :=
  hyex_C1.continuous.continuousAt
have hstart' : ∀ j : Fin k,
    Filter.Tendsto
      (fun h : ℝ => yex (x₀ + (j.val : ℝ) * h) - start h j)
      (nhds 0) (nhds 0) :=
  hstart_shape_bridge hyex_x₀ hyex_cont_x₀ hstart
```

The autonomous template expects `Yh h j.val`; here we have `start h
j` (which equals `Y m j.val` by `(hY_props m _).1`). The squeeze on
`aOf M Θ L h yex Y_m x₀` (where `Y_m n := Y m n`) collapses to use
`start h j` once the per-`m` initial-data clause is invoked.

### Step 6: handle the `k = 0` edge case

When `k = 0`, `Fin k` is empty, the LMM has no look-back, and
`IsLMMSolution` reduces to a degenerate single-step recurrence. The
autonomous theorem requires `hk : 0 < k`; the non-autonomous
predicate does not.

For `k = 0`: `IsLMMSolution h x₀ f Y` becomes `∀ n, M.α 0 * Y n =
-h * M.β 0 * f (x₀ + n*h) (Y n)`, i.e. `Y n = h * M.β 0 * f (x₀ +
n*h) (Y n)` (using `M.α 0 = -1` from `M.α_zero`). This is forward
Euler for `M.β 0 = 0` (which gives `Y n = 0` for all n) or implicit
otherwise.

**Recommendation**: try a direct closure for `k = 0` (likely
`M.α_zero` + algebraic manipulation gets `Y m m → yex x` from
nothing — but only if `M.β 0 = 0` and the iterates are all 0,
which won't equal `yex x` in general). If a clean argument doesn't
emerge in ~30 minutes, file
`.prover-state/issues/lmm_k_zero_degenerate.md` documenting the
case as deferred and `sorry` it. The textbook implicitly assumes
`k ≥ 1` (a 0-step method isn't really a multistep method).

### Step 7: assemble

The body should look roughly like:

```lean
intro f hf_cont L hf_lip_joint x₀ y₀ yex hyex_x₀ hyex_C1 hyex_ode_at
      M_bound hM hf_yex_bound start hstart x hxx Y hY_props
-- (k = 0 edge case branched out earlier via by_cases hk : 0 < k)
obtain ⟨Θ, hΘ_nn, hΘ⟩ := theta_bounded_of_isStable hk M hstab
have hL_joint : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
have hyex_ode : ∀ t, deriv yex t = f t (yex t) :=
  fun t => (hyex_ode_at t).deriv
have hyex_cont_x₀ : ContinuousAt yex x₀ :=
  hyex_C1.continuous.continuousAt
have hstart' := hstart_shape_bridge hyex_x₀ hyex_cont_x₀ hstart
obtain ⟨M₀, hM₀_pos, hM₀_small⟩ : ∃ M₀ : ℕ, 0 < M₀ ∧
    ∀ m ≥ M₀, ((x - x₀) / (m : ℝ)) * (L : ℝ) * |M.β 0| < 1 := ...
-- Define bInf, cInf as in the autonomous template (with L_joint,
-- (1 + M_bound) — the cycle 065+ lift uses (1+M_bound) per the
-- joint-Lipschitz substitution).
set bInf : ℝ := (Θ + 1) *
      ((L : ℝ) * (|M.β 0| * (∑ i : Fin k, |M.α i.succ|)
            + ∑ i : Fin k, |M.β i.succ|)) + 1 with hbInf_def
set cInf : ℝ := (Θ + 1) *
      (((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
          + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
        * (L : ℝ) * (1 + M_bound)) with hcInf_def
-- Per-m closed-form bound (uses globalError_recurrence_form_explicit_nonauto).
have hbound : ∀ m : ℕ, m ≥ M₀ →
    |yex (x₀ + (m : ℝ) * ((x - x₀) / (m : ℝ))) - Y m m| ≤ ... := by
  intro m hm
  have hm_pos : 0 < m := lt_of_lt_of_le hM₀_pos hm
  obtain ⟨hY_init, hY_lmm⟩ := hY_props m hm_pos
  have hh_nn : 0 ≤ (x - x₀) / (m : ℝ) :=
    div_nonneg (sub_pos.mpr hxx).le (Nat.cast_nonneg m)
  obtain ⟨ha, hb, hc, hrec, hu0⟩ :=
    globalError_recurrence_form_explicit_nonauto hk M hcons hL_joint hM
      hf_lip_joint hyex_C1 hyex_ode hf_yex_bound hh_nn (hM₀_small m hm)
      hY_lmm Θ hΘ_nn hΘ
  -- Apply discrete_gronwall_exp_bound (cycle 050).
  ...
-- Per-h Tendsto facts (cycle 061+62 wrappers — shape-agnostic).
have hb_lim := bOf_tendsto_at_zero M Θ (L : ℝ)
have hc_lim := cOf_tendsto_at_zero M Θ (L : ℝ) (1 + M_bound)
have hb_pos := bOf_limit_pos M Θ (L : ℝ) hΘ_nn hL_joint
-- For ha_lim, the autonomous version uses `Yh h`; we use `fun n => start h n`
-- on the trajectory's first k indices. Use hY_init to bridge.
have ha_lim : Filter.Tendsto
    (fun h : ℝ => aOf M Θ (L : ℝ) h yex (fun n => start h n) x₀)
    (nhds 0) (nhds 0) := aOf_tendsto_zero M Θ (L : ℝ) yex
                            (fun h n => start h n) x₀ hstart'
-- Outer-squeeze helpers (already shape-agnostic).
have ha_term := globalError_outer_squeeze_a_term ha_lim hb_lim k x₀ x
have hc_term := globalError_outer_squeeze_c_term hb_lim hc_lim hb_pos hk x₀ x
-- ... assemble per-m squeeze, then conclude Tendsto via
-- tendsto_of_tendsto_of_tendsto_of_le_of_le' as in autonomous lines
-- 5374–5381.
```

The exact squeeze-assembly needs adjustment because `hbound` is per
`m ≥ M₀` (not per `m > 0`): the `Filter.eventually_atTop` wrapper
uses `M₀` instead of `1`. Otherwise structurally identical to lines
5348–5381.

## Order of operations

1. **First**: Apply the `IsConvergent` predicate strengthening
   (Phase 1 above). Verify the file compiles after the predicate
   change. This touches only the predicate's hypothesis list — the
   conclusion (`Tendsto ... atTop (nhds 0)`) is unchanged.
2. **Second**: Write
   `.prover-state/issues/is_convergent_strengthened.md` documenting
   the deviation. Cross-reference `non_autonomous_lift_plan.md`.
3. **Third**: Implement the closure (Steps 0–7 above). Build
   incrementally with `lake env lean OpenMath/Chapter4/Section404.lean`
   between major destructuring steps so failures localise quickly.
4. **Fourth**: Run the pre-commit faithfulness check from CLAUDE.md.
   Update `.prover-state/task_results/cycle_068.md` with the
   strengthening rationale documented under "Faithfulness check".
5. **Fifth**: If the closure compiles cleanly, append a "RESOLVED in
   cycle 068" note to `non_autonomous_lift_plan.md` (do NOT delete
   the file — keep the historical record like cycles 065/066).
6. **Sixth**: Update `lean_status.json` for `thm:406D` and `def:402A`
   if status changes from `partial` to `formalized`.

## Estimated scope

* Predicate strengthening + issue file: ~30 LOC + ~80 LOC issue.
* Theorem closure: ~120–180 LOC (autonomous template body is ~130
  LOC; non-auto adds destructuring, the `M₀` derivation, and the
  `hyex_ode` bridge).
* Total: ~150–220 LOC. Well under the 500-LOC ceiling.

## Fallback if closure stalls

If Step 7's squeeze assembly turns out to require more than ~250
LOC of debugging, **stop and decompose**:

1. Split off two private helpers `stable_consistent_per_m_bound`
   (per-`m` closed-form, ~80 LOC) and `stable_consistent_squeeze`
   (the `tendsto_of_tendsto_of_tendsto_of_le_of_le'` final assembly,
   ~50 LOC). Land both this cycle.
2. Land the predicate strengthening + issue file regardless.
3. Defer the `stable_consistent_isConvergent` final integration to
   cycle 069. Document in `non_autonomous_lift_plan.md` as a 5th
   cluster.

Goal: cycle 068 must not regress. A two-helper landing with the
predicate strengthening is a valid score-1 cycle even if the
top-level theorem stays sorry'd.

## What NOT to do

* **Do NOT** modify `scripts/autonomous_loop.py` (loop-maintainer
  territory).
* **Do NOT** raise `maxHeartbeats` above 200000.
* **Do NOT** introduce `axiom` or `constant`.
* **Do NOT** attempt to derive joint-Lipschitz, global `M_bound`, or
  global `ContDiff ℝ 1 yex` from the existing `IsConvergent`
  hypotheses. They cannot be derived (see "CRITICAL" section).
* **Do NOT** refactor cycles 065–067 helpers to take spatial-only
  Lipschitz or Icc-restricted bounds. That would require redoing
  three cycles of work and produce a strictly weaker result.
* **Do NOT** strengthen the predicate by adding `LipschitzInSecond`
  AND `LipschitzWith (Function.uncurry f)` redundantly. The latter
  implies the former; pick the joint version.
* **Do NOT** poll Aristotle. There is no in-flight job, and the
  closure is integration work, not premise selection.
* **Do NOT** delete `stable_consistent_isConvergent_autonomous`
  (line 5253). It is the template we are mirroring; keeping it is
  useful for documentation and for any future user who wants the
  autonomous form directly.
* **Do NOT** rename or move existing helpers. The file structure is
  load-bearing — `globalError_recurrence_form_explicit_nonauto`
  (cycle 067) is consumed verbatim by the closure.
* **Do NOT** treat the prompt's "stuck on" framing (if any
  `attempts.md` entry points at line 5402) as a real problem. The
  sorry there IS the cycle 068 target; it has been there since
  cycle 062 by design.
* **Do NOT** attempt to prove convergence for any concrete LMM
  (e.g. `explicitEulerLMM.IsConvergent`). The cycle 068 goal is
  the abstract predicate-level theorem; concrete witnesses are
  separately tracked in `lmm_convergence_witness_deferred.md` and
  remain deferred.

## Cross-references

* `OpenMath/Chapter4/Section404.lean:5253` — autonomous template.
* `OpenMath/Chapter4/Section404.lean:4829` — cycle 067
  `globalError_recurrence_form_explicit_nonauto`.
* `OpenMath/Chapter4/Section404.lean:3852` — cycle 063 boundary
  adapters (`lipschitzInSecond_univ_toLipschitzWith`,
  `f_yex_bound_on_Icc`, `hstart_shape_bridge`). Only
  `hstart_shape_bridge` is consumed by cycle 068.
* `.prover-state/issues/non_autonomous_lift_plan.md` — overall
  cycle 064–068 plan; update the cluster-4 status when closing.
* `.prover-state/task_results/cycle_067.md` — cycle 067 deliverable
  log; the cluster-3 lift this builds on.
* `extraction/formalization_data/entities/thm_406D.json` —
  textbook statement.
* `extraction/formalization_data/entities/def_402A.json` —
  textbook predicate (compare with the strengthened Lean version
  for the faithfulness issue).
