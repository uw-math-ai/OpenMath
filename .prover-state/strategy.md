# Cycle 142 Strategy

## Status snapshot

* Sorry count: **0** (full Chapter 5 build green at `4154007`).
* No pending Aristotle results (Job A general-`n` `thm:550A` cancelled
  cycle 141 at 6 % after 24 h; treated as intractable).
* Cycle 141 score: +2 — heterogeneous-stages witness in §530.
* Recent string: cycles 137 (+2), 139 (+1), 140 (+2), 141 (+2). The
  reliable +score path has been **add a substantive witness to an
  existing predicate**.

## Decision: pivot from cycle-141's §442 recommendation to a §520 L-stability witness

Cycle 141's task results suggested opening Chapter 4 §442 (`def:442A`
principal sheet) "to spread chapter coverage". I am **overruling that
recommendation** for cycle 142.

Reason: I read `entities/def_442A.json` carefully. The textbook
statement bundles five distinct concepts (A-stable Φ, Riemann surface
`R_Φ`, order stars, order arrows, principal sheet) and the principal
sheet itself is defined as *"a neighbourhood of (0, 1) for which the
relationship between z and w is injective"* — i.e. a complex-analytic
local-injectivity condition on the Riemann surface of `Φ(w, z) = 0`.
Faithful Lean encoding requires:

* Two-variable complex polynomial / characteristic polynomial of the
  stability matrix (not yet wired up — `def:442A`'s Φ is LMM-side and
  differs from §520's `Φ_M`).
* Riemann surface infrastructure (the zero set viewed as a multi-sheet
  cover of ℂ; Mathlib has germs / `AnalyticAt` but no off-the-shelf
  Riemann-surface API).
* Local-injectivity predicate on a neighbourhood of `(0, 1)`.

This is multi-cycle infrastructure work, not a single-cycle witness
add.

The §530B/C alternatives (the natural follow-on from cycles 139/141)
are also expensive: `def:530B` requires defining "SM" (apply M after
applying S to y₀) and "ES" (apply S to the exact-solution shift) plus
a `O(h^{p+1})` comparison. Both `applyStartingMethod` and
`applyGLMStep` are ≈ 60 LOC each. Total ~250 LOC, with high risk that
the predicate ends up faithfulness-divergent.

**Better cycle-142 target**: complete the cycle-135/136/137 stability
witness story by adding the canonical **substantive L-stable witness:
backward Euler**. This is a textbook-canonical example, mirrors cycle
135's `implicitMidpointGLM_isAStable` pattern almost exactly, and
delivers a +2 score with low risk.

### Witness coverage gap this fixes

Current `IsLStable` witness story in `Section520.lean`:

| Witness | A-stable? | L-stable? | Substantive? |
|---|---|---|---|
| `trivialZeroGLM` (cycle 088) | ✓ | ✓ | NO (`M(z) ≡ 0` is vacuous) |
| `implicitMidpointGLM` (cycle 135/137) | ✓ | ✗ | yes (negative L-stab) |
| `explicitEulerGLM` (cycle 136/137) | ✗ | ✗ | yes (negatives) |
| **MISSING** | ✓ | ✓ | **canonical positive** |

Backward Euler with `M(z) = 1/(1−z)` is precisely the canonical
substantive positive witness: A-stable (`|1/(1−z)| ≤ 1` for
`Re(z) ≤ 0`) AND L-stable (`|M(z)| → 0` as `|z| → ∞`). Adding it
closes the 4-corner coverage matrix.

## Primary task — `backwardEulerGLM` + L-stability witness

### Step 1 — Define `backwardEulerGLM` in `Section510.lean`

Place next to `implicitMidpointGLM` (line ~218, before
`implicitMidpointGLM_isPreconsistent`). Keeps all canonical GLM
definitions in one file.

```lean
/-- The (1, 1) GLM realising backward Euler `y_{n+1} = y_n + h·f(y_{n+1})`.
The single stage `Y` satisfies `Y = U·y_n + h·A·f(Y) = y_n + h·f(Y)`,
and the output `y_{n+1} = V·y_n + h·B·f(Y) = y_n + h·f(Y) = Y`.
The all-ones tableau gives stability function `R(z) = 1/(1 − z)`,
the canonical Padé(0,1) approximant of `exp(z)`. -/
noncomputable def backwardEulerGLM : GeneralLinearMethod 1 1 where
  A := !![1]
  U := !![1]
  B := !![1]
  V := !![1]
```

### Step 2 — Closed-form stability matrix (in `Section520.lean`)

Append after the cycle-137 `implicitMidpointGLM_not_isLStable` block
(line ~580). Mirror cycle-135's
`implicitMidpointGLM_stabilityMatrix` (line 335-371) verbatim, swapping
`!![1 − z/2]` → `!![1 − z]` and `(2 − z) ≠ 0` → `(1 − z) ≠ 0`. Note
that here we want a *more general* hypothesis `z ≠ 1` (not just
`Re(z) ≤ 0`) because Step 5's cocompact-tendsto leg requires the
formula to hold on `‖z‖ → ∞` regions, which include large positive-real
`z`.

```lean
/-- Closed-form stability matrix for backward Euler at `z ≠ 1`:
    `M(z) = !![1 / (1 − z)]`. -/
theorem backwardEulerGLM_stabilityMatrix
    (z : ℂ) (hz : z ≠ 1) :
    backwardEulerGLM.stabilityMatrix z = !![1 / (1 - z)] := by
  have hne : (1 - z) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hA :
      (1 - z • complexify backwardEulerGLM.A) = !![1 - z] := by
    ext i j; fin_cases i; fin_cases j
    simp [backwardEulerGLM, complexify]
  unfold GeneralLinearMethod.stabilityMatrix
  rw [hA, Matrix.inv_subsingleton]
  ext i j; fin_cases i; fin_cases j
  simp [backwardEulerGLM, complexify, Matrix.mul_apply,
        Matrix.diagonal, Ring.inverse_eq_inv]
  rw [eq_div_iff hne]
  field_simp
  ring
```

### Step 3 — Magnitude bound for A-stability

```lean
/-- For `Re(z) ≤ 0`, `|1/(1 − z)| ≤ 1`. -/
theorem padeZeroOne_norm_le_one_of_re_nonpos
    {z : ℂ} (hz : z.re ≤ 0) :
    ‖(1 : ℂ) / (1 - z)‖ ≤ 1 := by
  have hre : (1 - z).re = 1 - z.re := by simp [Complex.sub_re]
  have hne : (1 - z) ≠ 0 := by
    intro h
    have : (1 - z).re = 0 := by rw [h]; simp
    rw [hre] at this; linarith
  have hbpos : 0 < ‖1 - z‖ := norm_pos_iff.mpr hne
  rw [norm_div, norm_one, div_le_one hbpos]
  -- Square both sides: 1 ≤ ‖1 − z‖² via normSq.
  have h_sq_ge : (1 : ℝ) ≤ ‖1 - z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have h2re : (1 - z).re = 1 - z.re := hre
    have h2im : (1 - z).im = -z.im := by simp [Complex.sub_im]
    rw [h2re, h2im]
    nlinarith [hz, sq_nonneg z.im, sq_nonneg z.re]
  have hb_nn : 0 ≤ ‖1 - z‖ := norm_nonneg _
  nlinarith [h_sq_ge, sq_nonneg (‖1 - z‖ - 1), hb_nn]
```

If the closing `nlinarith` balks at deriving `1 ≤ ‖1−z‖` from
`1 ≤ ‖1−z‖²`, fallback: use `Real.one_le_iff_one_le_sq` or
`abs_le_of_sq_le_sq` style.

### Step 4 — A-stability witness

```lean
theorem backwardEulerGLM_isAStable :
    backwardEulerGLM.IsAStable := by
  intro z hz
  -- z.re ≤ 0 ⇒ z ≠ 1.
  have hzne : z ≠ (1 : ℂ) := by
    intro h; rw [h] at hz; norm_num at hz
  refine ⟨1, ?_⟩
  intro k
  rw [backwardEulerGLM_stabilityMatrix z hzne]
  rw [norm_pow_fin_one]
  exact pow_le_one₀ (norm_nonneg _)
          (padeZeroOne_norm_le_one_of_re_nonpos hz)
```

### Step 5 — L-stability cocompact limit

This is the load-bearing analytical step. Two components:

(a) `‖z‖ → ∞` along `cocompact ℂ`. The Mathlib name is plausibly
    `tendsto_norm_cocompact_atTop` or `Filter.tendsto_norm_atTop_iff_cocompact`.
    Use `lean_local_search "cocompact"` and `lean_loogle "Tendsto _ (cocompact _)
    Filter.atTop"` to find the exact name. Backup: it can also be derived
    from `Bornology.cobounded_eq_cocompact` for proper metric spaces +
    `Metric.tendsto_cobounded_iff_norm_atTop`.

(b) `‖1/(1-z)‖ → 0` as `‖z‖ → ∞`. Standard chain via
    `‖1-z‖ ≥ ‖z‖ - 1` (reverse triangle, `norm_sub_norm_le` or
    `abs_norm_sub_norm_le`) plus `Tendsto.div`-style squeeze.

Concrete proof skeleton:

```lean
theorem backwardEulerGLM_isLStable :
    backwardEulerGLM.IsLStable := by
  refine ⟨backwardEulerGLM_isAStable, ?_⟩
  -- (a) z ≠ 1 eventually along cocompact ℂ.
  have h_eventually_ne :
      ∀ᶠ z in Filter.cocompact ℂ, z ≠ (1 : ℂ) := by
    have h_cpt : IsCompact ({1} : Set ℂ) := isCompact_singleton
    have := h_cpt.compl_mem_cocompact
    filter_upwards [this] with z hz
    intro hz1; exact hz (by rw [hz1]; rfl)
  -- (b) Bridge spectralRadius to ‖1/(1-z)‖ for z ≠ 1.
  have h_bridge :
      ∀ᶠ z in Filter.cocompact ℂ,
        spectralRadius ℂ (backwardEulerGLM.stabilityMatrix z)
          = (‖(1 / (1 - z) : ℂ)‖₊ : ENNReal) := by
    filter_upwards [h_eventually_ne] with z hz
    rw [backwardEulerGLM_stabilityMatrix z hz, spectralRadius_fin_one]
  -- (c) ‖1/(1-z)‖ → 0 cocompactly via ‖z‖ → ∞ + reverse triangle.
  rw [Filter.tendsto_congr' h_bridge]
  -- Goal: Tendsto (fun z => (‖1/(1-z)‖₊ : ENNReal)) cocompact (𝓝 0).
  -- Strategy: lift via ENNReal.tendsto_coe + ‖1/(1-z)‖ → 0 in ℝ≥0.
  sorry
```

The final `sorry` should close via:

1. `Tendsto (fun z => ‖z‖) cocompact atTop` (the cocompact name).
2. `‖1 - z‖ ≥ ‖z‖ - 1` (reverse triangle).
3. `‖1/(1 - z)‖ = 1/‖1 - z‖ ≤ 1/(‖z‖ - 1)` for `‖z‖ > 1`.
4. `Tendsto (fun r => 1/(r - 1)) atTop (𝓝 0)`.
5. Squeeze (`Tendsto.le_of_lt` style) + `ENNReal` lift.

If exact lemma names elude `lean_local_search`, factor out a
private helper

```lean
private theorem norm_one_div_sub_tendsto_zero_cocompact :
    Filter.Tendsto (fun z : ℂ => ‖(1 : ℂ) / (1 - z)‖)
      (Filter.cocompact ℂ) (nhds 0) := by
  ...
```

with its own focused proof, then compose. **DO NOT** introduce a
sorry in this helper; close it fully.

### Step 6 — Faithfulness check + plan.md + lean_status.json bump

* Document in the `backwardEulerGLM` docstring: textbook stability
  function `R(z) = 1/(1-z)` is Padé(0,1) of `exp(z)`. Cite Butcher
  §351 / §520 (BDF1) for the textbook source.
* No new sorry. No new axiom. No `maxHeartbeats` change.
* Update `plan.md` §520 row for `def:520F` to mention the new positive
  substantive witness.
* `extraction/formalization_data/lean_status.json` `def:520F` row
  cycle bumped to 142.

## What NOT to try

1. **Do NOT submit anything to Aristotle this cycle.** The Aristotle
   Job A history (24 h, 6 %, cancelled) shows large cycle-5 stability
   problems are flat. Backward Euler L-stability is too small to
   benefit from Aristotle parallelism, and the cycle-135 / cycle-137
   manual templates close it directly.
2. **Do NOT attempt `def:442A` principal sheet.** Riemann surface +
   local injectivity + complex-analytic order-star infrastructure is
   2–3 cycles minimum.
3. **Do NOT attempt `def:530B` order-relative-to-starting-method.**
   `applyStartingMethod` + `applyGLMStep` + `O(h^{p+1})` comparison
   is 200+ LOC with high faithfulness-divergence risk. Defer.
4. **Do NOT submit `thm:550A` general-`n` to Aristotle again.** Three
   cycles (138 partial, 140 n=2 stepping, 141 cancelled) confirm the
   eigenvalue-density / cofactor-induction is intractable for the
   prover. Per `thm_550A_general_n.md`, manual cofactor-expansion is
   the next path; this is a multi-cycle commitment.
5. **Do NOT add another `r > 2` heterogeneous-stages §530 witness.**
   Cycle 141's task results explicitly forbid this.
6. **Do NOT modify `scripts/autonomous_loop.py`.** The
   `tautology_scanner_false_positives.md` is loop-maintainer territory.
7. **Do NOT raise `maxHeartbeats`** above 200000.
8. **Do NOT introduce `axiom`** for any complex-analysis gap.
9. **Do NOT generalize `backwardEulerGLM` to a `(s, r) = (1, r)`
   family** (e.g. "padded backward Euler"). Stay at (1, 1) — the
   cycle-135 `implicitMidpointGLM` precedent shows that the canonical
   scalar witness is sufficient for non-vacuity, and cycles 133/134
   already exercised the `r = 2` shape for `IsRKStable`/`IsIRKStable`.
10. **Do NOT rename or refactor existing private helpers**
    (`fin_one_pow`, `norm_fin_one`, `norm_pow_fin_one`,
    `spectralRadius_fin_one`). Reuse them as-is.
11. **Do NOT route the L-stability proof through
    `Filter.tendsto_norm_atTop` from `Filter.atTop ℝ`** — `cocompact ℂ`
    requires the complex-norm version. Use the cocompact-side lemmas
    directly.

## Verification gates

Run all of these before claiming success. Cycle 138's score-`-2`
regression came from skipping the sorry-count check.

```bash
# 1. Sorry count must remain 0 across all of OpenMath/.
grep -rn '\bsorry\b' --include='*.lean' OpenMath/
# Expected: empty

# 2. Section510 + Section520 must build clean.
lake env lean OpenMath/Chapter5/Section510.lean
lake env lean OpenMath/Chapter5/Section520.lean

# 3. Full Chapter 5 build green.
lake build OpenMath.Chapter5

# 4. Axiom check on the three new theorems via mcp__lean-lsp__lean_verify:
#    OpenMath.Chapter5.Section520.backwardEulerGLM_stabilityMatrix
#    OpenMath.Chapter5.Section520.backwardEulerGLM_isAStable
#    OpenMath.Chapter5.Section520.backwardEulerGLM_isLStable
#    Expected: [propext, Classical.choice, Quot.sound] only — NO sorryAx.
```

## Backup plan (if Step 5's cocompact limit stalls)

If Step 5 is taking > 60 % of the cycle budget:

**Preferred fallback** — Land Steps 1–4 only (substantive A-stability
witness `backwardEulerGLM_isAStable`), defer L-stability. **DO NOT**
introduce a `sorry` in the file — instead, simply do not write
`backwardEulerGLM_isLStable` at all, and write a structured issue file
`.prover-state/issues/backwardEulerGLM_lstability_cocompact.md`
documenting:
- The cocompact-bridge attempt and what stalled.
- The Mathlib lemmas you tried and which exist / don't exist.
- A concrete plan for cycle 143 (the `norm_one_div_sub_tendsto_zero_cocompact`
  helper sketch).

This satisfies the "clean cycle, no sorry rise" rule (cycle 138's
score `-2` lesson). Sorry count stays at 0; A-stability witness is a
genuine +1 score; the deferred L-stability is properly scoped for
cycle 143.

**Anti-fallback** — DO NOT introduce a `sorry` in
`backwardEulerGLM_isLStable`. Cycle 138 was scored `-2` precisely for
sorry count rising 0→1; the same fate awaits this cycle if you ship a
sorry'd L-stability theorem.

## Suggested cycle-143 next target

Once L-stability lands (whether this cycle or 143):

* **Add `padded2DBackwardEulerGLM` r=2 witness** for `IsLStable`
  (mirrors cycles 133/134's `padded2DEulerGLM` for IRK-stability).
  Cheapest +score path.
* **Open `def:530B` with sorry-first scaffold** — having backward
  Euler in hand, we have a substantive concrete GLM to use for the
  trivial-witness `M.HasOrderRelativeTo trivialStartingMethod 0`.
  Medium risk.
* **Open `def:442A` Riemann-surface infrastructure** — high risk,
  multi-cycle. Defer until critical path requires it.

Pick based on cycle-142's actual closing time. If Steps 1–5 all close
cleanly in < 1 h, cycle 143 can attempt the padded r=2 witness as a
bonus.

## Pointers / lemma cheat sheet

* Cycle 135 reference proof: `Section520.lean:335–448` (`implicitMidpointGLM`
  closed-form + A-stability). **Copy this pattern verbatim.**
* Cycle 137 reference proof: `Section520.lean:531–589`
  (`implicitMidpointGLM_not_isLStable`). Reverses the spectral-radius
  argument; useful for understanding `spectralRadius_fin_one` usage.
* `Section520.lean:411–431`: private helpers `fin_one_pow`,
  `norm_fin_one`, `norm_pow_fin_one`. **In scope; reuse.**
* `Section520.lean:508–518`: private helper `spectralRadius_fin_one`.
  **In scope; reuse for Step 5.**
* Mathlib: `Matrix.inv_subsingleton`, `Ring.inverse_eq_inv`,
  `Complex.sub_re`, `Complex.sub_im`, `Complex.normSq_apply`,
  `Complex.sq_norm`, `norm_pos_iff`, `norm_nonneg`, `norm_div`,
  `norm_one`, `pow_le_one₀`, `IsCompact.compl_mem_cocompact`,
  `isCompact_singleton`.
* For Step 5 cocompact bridge, search:
  `lean_local_search "cocompact"` and
  `lean_loogle "Tendsto _ (Filter.cocompact _) Filter.atTop"`.
