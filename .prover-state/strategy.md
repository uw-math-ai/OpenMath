# Cycle 054 Strategy — autonomous-IVP Tendsto for `thm:406D`

## Status snapshot

- Cycle 053 landed `globalError_recurrence_form` and
  `globalError_closed_form_autonomous` axiom-clean, sorry count = 1
  (line 2603, the `stable_consistent_isConvergent` scaffold).
- The phantom "semantic sorry counter increased 0 → 1" verdict that
  capped cycle 053's score at -1 is a **scanner false positive**
  (line 1651 is in the existing infrastructure, not a vacuous proof).
  See `tautology_scanner_false_positives.md`. **Do not re-attack this**;
  it is a loop-maintainer concern.
- Aristotle: no pending results.

## Target — split into two steps within cycle 054

**Step A (REQUIRED):** Refactor `globalError_recurrence_form` to
remove the *trailing* `+ 1` slack from the constant `a`, so that
`a` scales linearly with `y'sum` (and therefore `a → 0` as
`y'sum → 0`). Without this, cycle 055's Tendsto theorem cannot
squeeze to 0 — see §"Why the slack must go" below.

**Step B (STRETCH):** State and prove the autonomous-IVP Tendsto
theorem `LinearMultistepMethod.stable_consistent_isConvergent_autonomous`
that consumes the cleaned-up bound and proves `Tendsto (fun m => Y m m
- yex x) atTop (𝓝 0)` for autonomous `f : ℝ → ℝ`. If Step A leaves
insufficient time, *state it with `sorry`* and document the closure
plan on its docstring; cycle 055 will close.

The existing `stable_consistent_isConvergent` (non-autonomous, line
2599) stays `sorry` for both this cycle and cycle 055 — it is the
non-autonomous bridge target for cycle 056+.

---

## Why the slack must go (Step A)

`globalError_recurrence_form` currently sets
```
set a : ℝ := (Θ + (Θ + 1) * Cbase * h * (k : ℝ) + 1) * y'sum + 1
```
(line 2153). The trailing `+ 1` is unnecessary:

* In `hu0` (line 2181-2191): the proof of `|yex x₀ - Y 0| ≤ a` only
  needs `y'sum ≤ (factor) * y'sum`, which holds because the factor
  is ≥ 1. The outer `+ 1` is unused slack.
* In the `n < k` branch (line 2240-2242): `Θ * y'sum ≤ a` reduces to
  `Θ ≤ (Θ + (Θ+1)·Cbase·h·k + 1)`, which is `0 ≤ (Θ+1)·Cbase·h·k + 1`,
  which holds without the outer `+ 1`.
* In `h_a_expand` (line 2515-2521): the calc chain uses
  `Θ·y'sum + (Θ+1)·Cbase·h·k·y'sum ≤ a`, which after dropping the
  outer `+ 1` becomes ≤ `(Θ + (Θ+1)·Cbase·h·k + 1)·y'sum`. The
  remaining slack (the inner `+ 1` multiplied by `y'sum`) suffices.

Why the slack BLOCKS cycle 055: in the closed-form bound
```
|ε(m)| ≤ exp(b·k·m·h_m)·a + (exp(b·k·m·h_m) − 1)·c·h_m/(b·k)
```
with `h_m := (x − x₀)/m`:
* `m·h_m = x − x₀` is constant, so `exp(b·k·m·h_m)` is bounded
  uniformly in `m`.
* `c·h_m/(b·k) → 0` as `m → ∞` (since `h_m → 0` and `b, c` are
  bounded).
* `a → 0` REQUIRES `a` to scale with `y'sum` (which → 0 by cycle
  049's `starting_error_sum_tendsto_zero`). With the trailing `+ 1`,
  `a → 1`, not 0, and the squeeze fails.

---

## Step A — concrete edits to `globalError_recurrence_form`

File: `OpenMath/Chapter4/Section404.lean`. Edits should be tightly
scoped to `globalError_recurrence_form` (lines ~2098–2540) and the
single consumer `globalError_closed_form_autonomous`
(lines ~2550–2579).

### Edit A1 — line 2153
```
- set a : ℝ := (Θ + (Θ + 1) * Cbase * h * (k : ℝ) + 1) * y'sum + 1 with ha_def
+ set a : ℝ := (Θ + (Θ + 1) * Cbase * h * (k : ℝ) + 1) * y'sum with ha_def
```

### Edit A2 — `ha_nn` (line 2160-2164)
Replace the body with a one-line `mul_nonneg` (factor is ≥ 1, y'sum ≥ 0):
```
have ha_nn : 0 ≤ a := by
  have h_factor_nn : 0 ≤ Θ + (Θ + 1) * Cbase * h * (k : ℝ) + 1 := by linarith
  exact mul_nonneg h_factor_nn hy'sum_nn
```

### Edit A3 — `hu0` proof (line 2181-2191)
Drop the trailing `+ 1`:
```
have hu0 : |yex x₀ - Y 0| ≤ a := by
  have h_factor_ge_1 : (1 : ℝ) ≤ Θ + (Θ + 1) * Cbase * h * (k : ℝ) + 1 := by
    have h1 : 0 ≤ Θ + (Θ + 1) * Cbase * h * (k : ℝ) := by
      linarith [hΘ_nn, hCbase_h_k_nn]
    linarith
  show |yex x₀ - Y 0| ≤ a
  calc |yex x₀ - Y 0|
      ≤ y'sum := hy0_le_sum
    _ = 1 * y'sum := by ring
    _ ≤ (Θ + (Θ + 1) * Cbase * h * (k : ℝ) + 1) * y'sum :=
        mul_le_mul_of_nonneg_right h_factor_ge_1 hy'sum_nn
```

### Edit A4 — `h_Θy_le_a` in the `n < k` branch (line 2240-2242)
Drop the `+ 1`:
```
have h_Θy_le_a : Θ * y'sum ≤ a := by
  show Θ * y'sum ≤ (Θ + (Θ + 1) * Cbase * h * (k : ℝ) + 1) * y'sum
  nlinarith [hy'sum_nn, hΘ_nn, hCbase_h_k_nn]
```

### Edit A5 — `h_a_expand` and `h_a_target` (line 2515-2521)
Drop the trailing `+ 1`:
```
have h_a_expand :
    a = Θ * y'sum + (Θ + 1) * Cbase * h * (k : ℝ) * y'sum + y'sum := by
  show (Θ + (Θ + 1) * Cbase * h * (k : ℝ) + 1) * y'sum = _
  ring
have h_a_target :
    Θ * y'sum + (Θ + 1) * Cbase * h * (k : ℝ) * y'sum ≤ a := by
  rw [h_a_expand]; linarith
```

After these five edits, `lake env lean OpenMath/Chapter4/Section404.lean`
should compile cleanly. The only consumer of `globalError_recurrence_form`
is `globalError_closed_form_autonomous` at line 2570; it should not
need modification, since it just destructures `⟨a, b, c, ...⟩`.

### Verify after Step A
1. `lake env lean OpenMath/Chapter4/Section404.lean` — clean.
2. `lean_verify` on
   `OpenMath.Chapter4.Section404.LinearMultistepMethod.globalError_closed_form_autonomous`
   — axioms `[propext, Classical.choice, Quot.sound]` only.
3. Sorry count unchanged at 1 (the line 2603 scaffold).

---

## Step B (STRETCH) — `stable_consistent_isConvergent_autonomous`

If Step A finishes early (likely in ~15 minutes — five small edits),
attempt Step B. If pressed for time, state with `sorry` and document.

### Statement (place near line 2598, *before* the existing
non-autonomous scaffold)

```lean
/-- **Autonomous-IVP form of Butcher Theorem 406D (cycle 054 step
toward `stable_consistent_isConvergent`).**

For an autonomous IVP `y' = f(y)` with `f` Lipschitz and `f∘yex`
bounded, a stable consistent LMM produces iterates that converge
to the exact solution as `h → 0`. This is the analytical core of
the textbook 406D; cycle 056+ will lift to non-autonomous `f`.

The proof composes:
* `globalError_closed_form_autonomous` (cycle 053) — exponential bound.
* `starting_error_sum_tendsto_zero` (cycle 049) — `y'sum → 0`.
* `Filter.Tendsto`-style squeeze. -/
theorem LinearMultistepMethod.stable_consistent_isConvergent_autonomous
    {k : ℕ} (hk : 0 < k) (M : LinearMultistepMethod k)
    (hcons : M.IsConsistent) (hstab : M.IsStable)
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {x₀ y₀ : ℝ} {yex : ℝ → ℝ}
    (hy0 : yex x₀ = y₀)
    (hyex_C1 : ContDiff ℝ 1 yex)
    (hyex_ode : ∀ t, deriv yex t = f (yex t))
    (hf_yex_bound : ∀ t, |f (yex t)| ≤ M_bound)
    {start : ℝ → Fin k → ℝ}
    (hstart : ∀ i : Fin k,
      Filter.Tendsto (fun h : ℝ => start h i) (nhds 0) (nhds y₀))
    (x : ℝ) (hxx₀ : x₀ < x)
    (Y : ℕ → ℕ → ℝ)
    (hY : ∀ m : ℕ, 0 < m →
      (∀ i : Fin k, Y m i.val = start ((x - x₀) / (m : ℝ)) i) ∧
      M.IsLMMSolution ((x - x₀) / (m : ℝ)) x₀ (fun _ y => f y) (Y m)) :
    Filter.Tendsto (fun m : ℕ => Y m m - yex x) Filter.atTop (nhds 0) := by
  sorry
```

The signature mirrors the non-autonomous `IsConvergent` definition
(line 305-322) but with autonomous `f : ℝ → ℝ` and `hf_lip` /
`hyex_ode` / `hf_yex_bound` as in `globalError_closed_form_autonomous`.

### Proof skeleton (for cycle 055 to close, OR attempt now if ample time)

The proof has five logical phases:

1. **Set up `h_m := (x - x₀) / m`.** Note `m * h_m = x - x₀` for
   `m > 0`. Use `eventually_atTop` to discard `m ≤ 0` (or `m < some
   m₀` such that `hsmall` holds).

2. **Verify `hsmall : h_m * L * |M.β 0| < 1` eventually.** Since
   `h_m → 0`, for sufficiently large `m` we have
   `h_m · L · |M.β 0| < 1`. Use `Filter.eventually_atTop`.

3. **Apply `globalError_closed_form_autonomous` at each `m`.**
   Destructure `⟨a, b, c, ha, hb, hc, h_bound⟩`. Note that `a, b, c`
   *depend on `m`* (since they depend on `h_m`). Name them
   `a_m, b_m, c_m` if needed.

4. **Bound the closed-form.** At `n = m, h = h_m`, the bound is
   ```
   |Y m m - yex x| ≤ exp(b_m · k · m · h_m) · a_m
                       + (exp(b_m · k · m · h_m) − 1) · c_m · h_m / (b_m · k)
   ```
   Note `m · h_m = x - x₀` (constant!), so
   `exp(b_m · k · m · h_m) = exp(b_m · k · (x - x₀))`.

5. **Prove each piece tends to 0:**
   * `b_m → b_∞` (some constant) since `Cbase` is `L · sum / (1 - h·L·|β₀|)`,
     which is continuous in `h` at `h = 0`. Use `Continuous.tendsto`
     plus `Filter.Tendsto.div`.
   * `exp(b_m · k · (x - x₀))` is bounded uniformly (continuous of
     bounded `b_m`).
   * `a_m → 0`: `a_m = (Θ + (Θ+1)·Cbase_m·h_m·k + 1)·y'sum_m`. The
     factor → `Θ + 1` (bounded). `y'sum_m = Σ_{i:Fin k}
     |yex(x₀ + i·h_m) − start(h_m, i)| → 0` by
     `starting_error_sum_tendsto_zero` (cycle 049). Hence `a_m → 0`.
   * `c_m · h_m / (b_m · k) → 0`: `c_m` is bounded, `b_m·k` is bounded
     below by 1·k > 0, and `h_m → 0`. So this → 0.
   * Sum tends to 0; `squeeze_zero` closes.

### Concrete Mathlib lemmas

| Need | Lemma |
|------|-------|
| `(x - x₀)/m → 0` as `m → ∞` | `tendsto_const_div_atTop_nhds_zero_nat` (or compose `div` with `Nat.cast_atTop`) |
| `eventually` on filter via `<` | `Filter.eventually_atTop` |
| Sum of two tendsto | `Filter.Tendsto.add` |
| Product with bounded → 0 | `Filter.Tendsto.mul` (need `Filter.Tendsto.const_mul` or bounded × → 0) |
| Squeeze | `squeeze_zero` |
| `start h i → y₀` lifted to `y'sum_m → 0` | `starting_error_sum_tendsto_zero` (already in file at line 1851) |
| Continuity of `1/(1 - h·L·|β₀|)` at h=0 | `Continuous.div` + `continuous_const_sub` |

### What NOT to attempt for Step B closure

* **Do NOT** try to prove the *non-autonomous* `IsConvergent` form
  in this cycle. That requires generalising the cycle 045–052 helper
  chain to non-autonomous `f`, which is multi-cycle infrastructure.
* **Do NOT** attempt to prove the autonomous theorem with
  `f : ℝ → ℝ → ℝ` shape and a side-axiom that `f` is autonomous —
  that's a definitional shim, not a real proof.
* **Do NOT** raise `maxHeartbeats` if the squeeze argument is slow.
  Decompose into helpers like `_v_a_tendsto_zero`,
  `_v_c_h_tendsto_zero`, `_v_b_bounded` instead.

---

## What NOT to do this cycle

* **Do NOT** chase the "semantic sorry counter 0 → 1" verdict from
  cycle 053's evaluation. It is a scanner false positive on line
  1651, which is unchanged infrastructure. Cycle 015 already filed
  `tautology_scanner_false_positives.md`; it remains the loop
  maintainer's responsibility. Worker should not edit
  `scripts/autonomous_loop.py`.
* **Do NOT** attempt to remove or rename `globalError_recurrence_form`'s
  signature in any way other than the `+ 1` slack edit. The five
  helpers (`recentSum_swap_bound`, `globalError_per_step_sum_form`,
  `globalError_eq_linRec`, `globalError_closed_form`,
  `discrete_gronwall_exp_bound`) all consume the existing shape.
* **Do NOT** reintroduce the trailing `+ 1` slack to "make a `linarith`
  shorter" — it would re-block cycle 055.
* **Do NOT** edit cycles 045–052 helpers. They are stable.
* **Do NOT** introduce `axiom` / `constant` to bypass the autonomous
  restriction.
* **Do NOT** poll Aristotle. No submissions are pending; no infrastructure
  ask is suitable for Aristotle (the slack removal is a 5-line refactor;
  the squeeze argument is filter manipulation, not premise selection).

---

## Aristotle plan

**Skip Aristotle this cycle.** The Step A refactor is too small to
justify a submission (5 short edits, each ~3 lines). The Step B
squeeze argument is filter-manipulation (`Filter.Tendsto.add`,
`Filter.Tendsto.mul`, `squeeze_zero`) where Aristotle's premise
selection has historically struggled. Manual proof is the more
reliable path. Save Aristotle compute for the cycle 056+
non-autonomous bridge, where the work is more substantial.

---

## Acceptance criteria for cycle 054

**Required (Step A only):**
- `OpenMath/Chapter4/Section404.lean` compiles cleanly.
- `globalError_recurrence_form` no longer has the trailing `+ 1`
  slack on `a`.
- `globalError_closed_form_autonomous` continues to compile and
  remains axiom-clean.
- Sorry count unchanged (1 sorry, the line 2603 scaffold).

**Stretch (Step A + Step B-state-only):**
- Above, plus `stable_consistent_isConvergent_autonomous` is
  declared in the file with `sorry` body and a docstring describing
  the proof skeleton.
- Sorry count rises to 2.

**Full stretch (Step A + Step B-closed):**
- Above, plus `stable_consistent_isConvergent_autonomous` is closed.
- `lean_verify` shows axiom set
  `[propext, Classical.choice, Quot.sound]`.
- Sorry count returns to 1.

---

## Faithfulness check (must run pre-commit)

The slack removal in Step A does NOT change any user-facing definition
or theorem signature; it tightens an internal helper. No
faithfulness divergence introduced.

If Step B is closed:
* `stable_consistent_isConvergent_autonomous` — what does it
  capture relative to `thm:406D`?
  * **Textbook (`thm_406D.json`):** "A stable consistent linear
    multistep method is convergent."
  * **Lean theorem:** captures the textbook conclusion *only* for
    autonomous `f : ℝ → ℝ`. The non-autonomous form is a strict
    superset; cycle 056+ closes that gap.
  * **Justification for divergence:** the cycle 045–052 helper
    chain is autonomous-only by construction. Generalising is
    multi-cycle infrastructure work; the autonomous form is the
    analytical core and a faithful subset.
  * **No definition smuggling**: `IsConvergent` is the textbook
    definition; the autonomous theorem produces the textbook
    conclusion (the Tendsto) under a strict subset of its
    hypotheses.
* TAUTOLOGY check: conclusion is `Filter.Tendsto … (nhds 0)`, not
  any hypothesis. ✓
* IDENTITY check: proof is a substantive squeeze argument
  composing five separate analytical facts. Not vacuous. ✓
* HYPOTHESIS STRENGTH: the autonomous restriction is documented in
  the docstring; the `hsmall : h * L * |M.β 0| < 1` requirement
  becomes "eventually true as h → 0" which is automatic.

---

## Summary

1. **Step A (must do):** Remove trailing `+ 1` slack from `a` in
   `globalError_recurrence_form` — five small edits, all in
   lines 2153–2521. Verify clean build + axiom-clean.
2. **Step B (stretch):** Declare/state
   `stable_consistent_isConvergent_autonomous`. If time permits,
   close via the squeeze skeleton above; otherwise leave as `sorry`
   with the proof skeleton in the docstring.
3. **What NOT to do:** Don't chase the scanner phantom. Don't
   touch helpers from cycles 045–052. Don't reach for the
   non-autonomous form. Don't poll Aristotle.

End-of-cycle deliverable target: clean compile, sorry count ≤ 2
(one for the existing scaffold, optionally one for the new
autonomous declaration), and the closed-form bound is now in a
shape that cycle 055's squeeze can consume.
