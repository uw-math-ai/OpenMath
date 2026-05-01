---
name: Consultant advice — cycle 040 (lem:406B sorry-first scaffold)
description: Diagnoses the "commits not reaching repo" verdict as the same stale phantom seen in cycles 008/014/015; independently verifies Butcher's textbook typo; gives proof plans for the 4 remaining sub-lemmas and the main bound.
type: project
---

# Consultant advice — cycle 040: the "commit failure" verdict is another stale phantom; the 5 sorries ARE expected; Aristotle still IN_PROGRESS; concrete proof plans for A/B/C/D + main below

Author: consultant subagent.
Date: 2026-04-30.
Phase at time of writing (per `heartbeat.json`): cycle 040, post-worker.
Branch tip: `4154007 Cycle 040 — lem:406B sorry-first scaffold + sub-lemma E proved`.
Aristotle project: `53d674e4-20e3-43e8-9600-0b189c62c8f5` — `IN_PROGRESS` at 4 % (created 22:08, last update 23:12 UTC, ≈ 1 h elapsed).

---

## A. The "commit failure" framing is wrong — cycle 040 IS committed

The prompt's claim
> Git commit/push failure: the worker's local work
> (`OpenMath/Chapter4/Section404.lean` and related files) did not land
> in the repository.

is **demonstrably false**, in the same way that cycles 008/014/015 had
demonstrably-false `attempts.md` carry-over verdicts (see
`consultant_advice_cycle_009.md` §A and
`consultant_advice_cycle_015.md` §B):

```
$ git log --oneline -3
4154007 Cycle 040 — lem:406B sorry-first scaffold + sub-lemma E proved
424280d Source .env in launch scripts so Telegram alerts actually fire
b654fc7 Add blueprint/sync_leanok.py to drive dep graph from lean_status.json

$ git rev-parse HEAD
4154007f82cf78dcd24957c16e1199a8bed34d19

$ git rev-parse origin/Main/Experiments
4154007f82cf78dcd24957c16e1199a8bed34d19

$ git show --stat 4154007 | head -10
... 8 files changed, 1304 insertions(+), 285 deletions(-)
... .prover-state/aristotle_submissions/cycle_040/decomposition_attempt.lean | 106 ++
... .prover-state/aristotle_submissions/cycle_040/sub_lemmas.lean | 113 ++
... .prover-state/issues/lem_406B_textbook_check.md | 115 +++
... .prover-state/strategy.md | 575 ++++++++--
... .prover-state/task_results/cycle_040.md | 175 +++
... OpenMath/Chapter4/Section404.lean | 212 +++
... extraction/formalization_data/lean_status.json | 6 +-
```

Local HEAD = `origin/Main/Experiments` = `4154007`. Real diff
(`+1304 / -285` across 8 files) lands every artifact described in
`task_results/cycle_040.md`: the sorry-first scaffold, sub-lemma E's
manual proof, the textbook-typo issue file, the Aristotle submission
file, and the lean_status.json bump.

The five sorry locations (`Section404.lean:525, 541, 559, 577, 692`)
are **expected sorry-first placeholders** for sub-lemmas A, B, C, D
and the main theorem `localTruncationError_bound`. They were
explicitly enumerated in cycle 040's task results §"Result" and
§"Suggested next approach". Their existence is the *cycle's planned
deliverable shape* (per CLAUDE.md "structure + 2 sub-lemmas closed"
ceiling), not evidence of a commit failure.

**Same root cause as cycles 008/014/015.** The supervisor's
prompt-builder appears to be reading "stuck" rows from a stale
source rather than re-running diagnostics against `HEAD` after the
worker commits. The pattern is now well-documented; see
`consultant_advice_cycle_014.md` §D3 and
`tautology_scanner_false_positives.md` for the standing fix
recommendation. **This is loop-maintainer territory, not worker
territory.**

---

## B. Independent algebraic verification of Butcher's textbook typo

I re-derived both candidate decompositions from scratch, without
reading the cycle 040 issue file's algebra, and reached the same
conclusion. Recording the derivation here so the worker / planner
have an independent confirmation.

### Setup

Definition (def:406A):
```
L(y, x, h) = y(x) − Σ_{i=1}^k α_i y(x − ih) − h Σ_{i=0}^k β_i y'(x − ih)
```

Preconsistency (404a): `Σ_{i=1}^k α_i = 1`.
Consistency (404b): `Σ_{i=1}^k i·α_i = Σ_{i=0}^k β_i`.
Derived: `Σ_{i=1}^k (i·α_i − β_i) = β_0` (subtract Σ_{i≥1} β_i).

### Butcher's claimed RHS (textbook):

```
R₁ = Σ_{i=1}^k α_i [y(x) − y(x−ih) − ih y'(x)]
     + h Σ_{i=1}^k (i·α_i − β_i)[y'(x) − y'(x−ih)]
```

Expanding:
```
R₁ = (Σα_i) y(x) − Σα_i y(x−ih) − h y'(x) (Σ i·α_i)
     + h y'(x) (Σ(i·α_i − β_i)) − h Σ(i·α_i − β_i) y'(x−ih)
   = y(x) − Σα_i y(x−ih)                     [preconsistency]
       + h y'(x) [β_0 − Σ i·α_i]              [(404b) collapse]
       − h Σ_{i=1}^k (i·α_i − β_i) y'(x−ih)
```

Coefficient of `y'(x)` in R₁: `h(β_0 − Σ_{i=1}^k iα_i) = h(β_0 − Σ_{i=0}^k β_i)
                                                       = −h Σ_{i=1}^k β_i`.

Coefficient of `y'(x)` in L (i.e. the i=0 term of L's β-sum):
`−h β_0`.

For R₁ = L we'd need `−h Σ_{i=1}^k β_i = −h β_0`, i.e.
`Σ_{i=1}^k β_i = β_0` — **not true in general**.

#### Counter-example: explicit Euler (k=1, α₁=1, β₀=0, β₁=1)

* `Σ_{i=1}^k β_i = 1 ≠ 0 = β_0`. Mismatch.
* Direct check at this method:
  `L = y(x) − y(x−h) − h(0)y'(x) − h(1)y'(x−h) = y(x) − y(x−h) − h y'(x−h)`.
  `R₁ = 1·[y(x) − y(x−h) − h y'(x)] + h·(1·1 − 1)·[y'(x) − y'(x−h)]
      = y(x) − y(x−h) − h y'(x)`.
  `R₁ − L = h y'(x−h) − h y'(x) ≠ 0`. ❌

So Butcher's claimed decomposition fails, on the simplest possible
LMM.

### The corrected RHS (β_i form):

```
R₂ = Σ_{i=1}^k α_i [y(x) − y(x−ih) − ih y'(x)]
     + h Σ_{i=1}^k β_i [y'(x) − y'(x−ih)]
```

Expanding (using `Σ α_i = 1` and `Σ_{i=1}^k i·α_i = Σ_{i=0}^k β_i`):
```
R₂ = y(x) − Σα_i y(x−ih) − h y'(x) (Σ_{i=0}^k β_i)
       + h y'(x) (Σ_{i=1}^k β_i) − h Σ_{i=1}^k β_i y'(x−ih)
   = y(x) − Σα_i y(x−ih)
       − h y'(x) [Σ_{i=0}^k β_i − Σ_{i=1}^k β_i]
       − h Σ_{i=1}^k β_i y'(x−ih)
   = y(x) − Σα_i y(x−ih) − h β_0 y'(x) − h Σ_{i=1}^k β_i y'(x−ih)
   = L. ✓
```

The `β_i` form is correct.

#### Sanity check on explicit Euler:
`R₂ = 1·[y(x) − y(x−h) − h y'(x)] + h·1·[y'(x) − y'(x−h)]
    = y(x) − y(x−h) − h y'(x−h) = L. ✓`

### Implication for the bound

The corrected bound coefficient is `Σ_{i=1}^k i |β_i|`, not Butcher's
`Σ_{i=1}^k i |i α_i − β_i|`. Cycle 040's encoded statement matches
this corrected form. **Worker's diagnosis confirmed.**

I'd also flag that the worker should consider footnoting this
explicitly in the docstring of `localTruncationError_bound` (it
already does, via the `§406` block header — that is sufficient).

### Aside: is Butcher's stated bound *also* a valid upper bound, just
proved by a different route?

For most (preconsistent + consistent) methods we have no a-priori
relation between `Σ i |β_i|` and `Σ i |i α_i − β_i|`. Either could be
larger. So they are *different* bounds — one is not always tighter.
Butcher's bound *might* still hold on individual methods, but its
proof in the textbook is via the broken decomposition, so we cannot
claim it without a fresh proof. The β_i form is what we should
formalise; doing otherwise would be a faithfulness divergence with
no proof.

---

## C. Aristotle status

Project `53d674e4-20e3-43e8-9600-0b189c62c8f5` — `IN_PROGRESS` at
**4 %** as of 23:12 UTC (≈ 1 h after submission at 22:08 UTC).
Sub-lemmas A, B, C, D, E were all submitted; sub-lemma E is already
proved by the worker (so a returned proof would be "wasted" but
harmless).

**Recommendation for cycle 041 polling cadence.** The CLAUDE.md
"sleep 30 min, check once, then proceed" rule is appropriate here.
Cycle 041 should:

1. Run `mcp__aristotle__get_status` once at the start of the
   cycle. If still `IN_PROGRESS` and < 50 %, treat Aristotle as
   "not yet contributing" and proceed to manual proof of the
   easiest remaining sub-lemma (D — see §D.4 below).
2. If returned proofs exist, extract them and incorporate. If a
   returned proof for E exists (we already have one), keep the
   manual one — it has a known shape and depends on identifiable
   Mathlib lemmas (good for reproducibility).
3. Do NOT wait > 1 h on Aristotle in cycle 041. The submission has
   already had a full 30-min sleep window from cycle 040; another
   hour-of-cycle waiting is wasted compute.

---

## D. Concrete proof plans for the 4 remaining sub-lemmas + main

These are detailed enough that the worker can attempt manual proofs
of A and D in cycle 041 even if Aristotle is still 0 %, and B/C in
cycles 042 / 043. The main theorem `localTruncationError_bound` is
final integration, deferrable to whichever cycle has all of A/B/C/D
in hand.

Throughout this section I use the file's variable names from
`Section404.lean:516–577` and `Section404.lean:678–692`.

### D.1 — Sub-lemma A `exact_solution_norm_bound`

Goal:
```
|y (x + h * ξ) - y x| ≤ h * (-ξ) * M_bound
```
under `hh : 0 ≤ h`, `hξ : ξ ≤ 0`, `hy_diff : Differentiable ℝ y`,
`hy_ode : ∀ t, deriv y t = f (y t)`, `hf_y_bound : ∀ t, |f (y t)| ≤ M_bound`,
`hM : 0 ≤ M_bound`.

#### Mathematical argument

By FTC,
```
y(x + hξ) − y(x) = ∫_{x}^{x + hξ} y'(t) dt = ∫_{x}^{x + hξ} f(y(t)) dt.
```
For `ξ ≤ 0`, the integration interval `[x + hξ, x]` has length `−hξ`
(non-negative since `h ≥ 0` and `−ξ ≥ 0`).
`intervalIntegral` in Mathlib is signed (so the value of
`∫ x in a..b, ·` flips when `a > b`); the magnitude bound is
oriented via `|b − a|` and is symmetric in `a, b`.

Using `intervalIntegral.norm_integral_le_of_norm_le_const` (Mathlib,
`Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:737`):
```
‖∫ x in a..b, f x‖ ≤ C * |b - a|     when  ∀ x ∈ Ι a b, ‖f x‖ ≤ C
```
gives
```
|∫ t in x..(x+hξ), f(y(t)) dt| ≤ M_bound * |hξ|.
```
Then `|hξ| = h * (-ξ)` since `h ≥ 0` and `-ξ ≥ 0`.

#### Lean tactic plan

```lean
lemma exact_solution_norm_bound
    {f : ℝ → ℝ} {M_bound : ℝ} (hM : 0 ≤ M_bound)
    {y : ℝ → ℝ}
    (hy_diff : Differentiable ℝ y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (x h : ℝ) (hh : 0 ≤ h)
    (ξ : ℝ) (hξ : ξ ≤ 0) :
    |y (x + h * ξ) - y x| ≤ h * (-ξ) * M_bound := by
  -- Step 1: rewrite as an integral via FTC.
  have hderiv : ∀ t ∈ Set.uIcc x (x + h * ξ), HasDerivAt y (f (y t)) t := by
    intro t _
    have ht := (hy_diff.differentiableAt (x := t)).hasDerivAt
    rw [hy_ode] at ht
    exact ht
  have hint : IntervalIntegrable (fun t => f (y t)) MeasureTheory.volume
              x (x + h * ξ) := by
    apply Continuous.intervalIntegrable
    -- f ∘ y is continuous since both factors are.
    -- A simpler route: use `LipschitzWith` continuity in the
    -- main theorem's context. Here we don't have hf_lip, so use:
    -- |f (y t)| ≤ M_bound implies measurability + integrability on a
    -- compact interval suffices via `IntervalIntegrable.bdd_const`.
    sorry  -- Aristotle / fallback: use ContinuousOn from Differentiable.continuous (hy_diff) + LipschitzWith argument from caller
  have hFTC :
      ∫ t in x..(x + h * ξ), f (y t) = y (x + h * ξ) - y x := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simpa using this
  -- Step 2: bound by the constant M_bound.
  have hbound :
      |∫ t in x..(x + h * ξ), f (y t)| ≤ M_bound * |h * ξ - 0| := by
    -- norm_integral_le_of_norm_le_const wants `∀ t ∈ Ι a b, |f (y t)| ≤ M_bound`.
    have hC : ∀ t ∈ Set.uIoc x (x + h * ξ), ‖f (y t)‖ ≤ M_bound := by
      intro t _
      simpa [Real.norm_eq_abs] using hf_y_bound t
    have := intervalIntegral.norm_integral_le_of_norm_le_const hC
    simpa [Real.norm_eq_abs, sub_eq_add_neg, add_comm, add_left_comm] using this
  -- Step 3: rewrite |h * ξ| as h * (-ξ).
  have habs : |h * ξ - 0| = h * (-ξ) := by
    rw [sub_zero]
    rw [abs_mul, abs_of_nonneg hh, abs_of_nonpos hξ, neg_eq_zero.not.mpr]
    -- or: rw [abs_mul, abs_of_nonneg hh]; rw [abs_of_nonpos hξ]
    sorry  -- finalize: h * |ξ| = h * (-ξ)
  rw [← hFTC]
  calc |∫ t in x..(x + h * ξ), f (y t)|
      ≤ M_bound * |h * ξ - 0| := hbound
    _ = M_bound * (h * (-ξ)) := by rw [habs]
    _ = h * (-ξ) * M_bound := by ring
```

#### Concrete refinements of the two `sorry`s above:

* For `hint` (integrability): the cleanest closure is
  `(hy_diff.continuous.comp continuous_id).comp_intervalIntegrable …`
  — but `f ∘ y` is what we need integrable, not `y`. We need
  `Continuous (fun t => f (y t))`. From `hy_ode` and `hy_diff`,
  `fun t => f (y t) = deriv y` (extensionally). So:
  ```lean
  have hcont : Continuous (fun t => f (y t)) := by
    have heq : (fun t => f (y t)) = deriv y := by funext t; exact (hy_ode t).symm
    rw [heq]
    -- Now we need Continuous (deriv y). This is NOT free from
    -- Differentiable ℝ y alone — y could be differentiable but with
    -- a discontinuous derivative.
    sorry
  ```
  This exposes a real signature gap: the statement is provable only
  if `f ∘ y` (equivalently `deriv y`) is continuous. **Recommend
  strengthening the hypothesis to `Continuous (deriv y)` or
  `ContDiff ℝ 1 y`** (the latter is cleaner). The textbook implicitly
  assumes the exact solution is `C¹`. Adding this is a faithful
  hypothesis (the IVP `y' = f∘y` with Lipschitz `f` already implies
  `y ∈ C¹`, so this isn't a strengthening relative to the textbook —
  it's just making explicit what was implicit).
* For `habs`: `abs_mul` + `abs_of_nonneg hh` + `abs_of_nonpos hξ`
  gives `|h * ξ| = h * (-ξ)`. The current attempt is over-complicated;
  should be just two rewrites.

#### Aristotle suitability

This sub-lemma is the type Aristotle handles well (canonical FTC +
norm bound + abs arithmetic). The signature gap on `Continuous
(deriv y)` is the main risk; Aristotle may struggle to recognise
the gap and introduce the `ContDiff` hypothesis itself.
Recommend adding `(hy_C1 : Continuous (deriv y))` as a hypothesis to
sub-lemma A *before* re-submitting if Aristotle fails — that turns
this into a clean ≤ 10-line proof.

#### Mathlib lemmas to feed to Aristotle / use manually

| Goal | Lemma | File |
|---|---|---|
| FTC: `∫ y' = y(b) − y(a)` | `intervalIntegral.integral_eq_sub_of_hasDerivAt` | `MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean` |
| Norm bound on signed integral | `intervalIntegral.norm_integral_le_of_norm_le_const` | `MeasureTheory/Integral/IntervalIntegral/Basic.lean:737` |
| Continuity from differentiability | `Differentiable.continuous` | std |
| Continuous → IntervalIntegrable | `Continuous.intervalIntegrable` | std |
| `|h ξ| = h (−ξ)` for `h ≥ 0, ξ ≤ 0` | `abs_mul`, `abs_of_nonneg`, `abs_of_nonpos` | std |

---

### D.2 — Sub-lemma B `residual_integral_form`

Goal:
```
y x - y (x - i*h) - (i*h) * deriv y x
  = h * ∫ ξ in (-(i:ℝ))..0, (f (y (x + h*ξ)) - f (y x))
```

#### Mathematical argument

Two FTC applications + change of variables:

1. By FTC, `y x - y (x - i*h) = ∫ t in (x - i*h)..x, deriv y t dt
                              = ∫ t in (x - i*h)..x, f (y t) dt`.
2. Change of variables `t = x + h*ξ` (so `dt = h dξ`, and as
   `t` ranges over `[x - i*h, x]`, `ξ` ranges over `[-i, 0]`):
   `∫ t in (x - i*h)..x, f (y t) dt = h * ∫ ξ in (-i)..0, f (y (x + h*ξ)) dξ`.
3. The `(i*h) * deriv y x` term is `(i*h) * f(y(x))`, which equals
   `h * ∫ ξ in (-i)..0, f(y(x)) dξ` (the integrand is constant).
4. Subtract: result is `h * ∫_{-i}^0 [f (y (x + h ξ)) - f (y x)] dξ`.

#### Lean lemmas

* FTC: `intervalIntegral.integral_eq_sub_of_hasDerivAt`.
* Change of variables (for affine reparam): the cleanest tool is
  `intervalIntegral.smul_integral_comp_mul_add` (Mathlib,
  `MeasureTheory/Integral/IntervalIntegral/Basic.lean:909`):
  ```
  c • ∫ x in a..b, f (c * x + d) = ∫ x in c*a + d..c*b + d, f x
  ```
  Set `c = h, d = x, a = -i, b = 0`: get
  `h * ∫ ξ in (-i)..0, f (y (h*ξ + x)) = ∫ t in (h*(-i)+x)..(h*0+x), f (y t)`,
  i.e. `h * ∫ ξ in (-i)..0, f(y(x + h*ξ)) = ∫ t in (x - h*i)..x, f(y t)`.
* Constant integral: `intervalIntegral.integral_const`:
  `∫ _ in a..b, c = (b - a) • c`. Set `a = -i, b = 0, c = f(y x)`:
  `∫ _ in (-i)..0, f(y x) = i • f(y x) = i * f(y x)`. So
  `h * ∫ _ in (-i)..0, f(y x) = h * i * f(y x) = (i*h) * deriv y x`
  by `hy_ode x`.

#### Lean tactic plan

```lean
lemma residual_integral_form
    {f : ℝ → ℝ} {y : ℝ → ℝ}
    (hy_diff : Differentiable ℝ y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (i : ℕ) (x h : ℝ) (hh : 0 ≤ h) :
    y x - y (x - (i : ℝ) * h) - ((i : ℝ) * h) * deriv y x
      = h * ∫ ξ in (-(i : ℝ))..0, (f (y (x + h*ξ)) - f (y x)) := by
  -- Step 1: deriv y t = f (y t) pointwise; rewrite RHS integrand.
  -- Step 2: split integral over difference into difference of integrals.
  rw [intervalIntegral.integral_sub]
  ring_nf
  -- Step 3: handle the constant integral ∫ _ in (-i)..0, f (y x) = i * f (y x).
  rw [intervalIntegral.integral_const]
  -- Step 4: handle the substitution h * ∫ ξ in (-i)..0, f(y(x + hξ))
  --        = ∫ t in (x - i*h)..x, f(y t) via smul_integral_comp_mul_add.
  -- Step 5: apply FTC: ∫ t in (x - i*h)..x, f(y t) = y x - y(x - i*h)
  --        via integral_eq_sub_of_hasDerivAt and hy_ode.
  sorry  -- ~15 lines combining the above
```

The full proof is ~20 lines once the change-of-variables direction
is correct. Aristotle should handle this if its premise selection
finds `smul_integral_comp_mul_add` — that lemma is the load-bearer.

#### Mathlib lemmas

| Goal | Lemma | File |
|---|---|---|
| FTC for derivatives | `intervalIntegral.integral_eq_sub_of_hasDerivAt` | as above |
| Affine change of variables | `intervalIntegral.smul_integral_comp_mul_add` | `Basic.lean:909` |
| Constant integral | `intervalIntegral.integral_const` | `Basic.lean:802` |
| Difference of integrals | `intervalIntegral.integral_sub` | std |

#### Aristotle suitability

This is the most challenging sub-lemma for Aristotle (multiple FTC
applications + change of variables) but it is also the most
"textbook standard" of the four — the proof is exactly Butcher's
written argument. Submit with the hint
`smul_integral_comp_mul_add` in the prompt next round. If
Aristotle fails, this is the right place to spend manual effort
(it is the only sub-lemma that requires real Mathlib FTC plumbing).

---

### D.3 — Sub-lemma C `residual_bound`

Goal:
```
|y x - y (x - i*h) - (i*h) * deriv y x| ≤ (1/2) * (i:ℝ)^2 * h^2 * L * M_bound
```

#### Mathematical argument

Combine sub-lemma B and sub-lemma A and Lipschitz.

```
|residual|
  = h * |∫_{-i}^0 [f(y(x + hξ)) - f(y(x))] dξ|       [by B]
  ≤ h * ∫_{-i}^0 |f(y(x + hξ)) - f(y(x))| dξ          [norm_integral_le_integral_norm]
  ≤ h * ∫_{-i}^0 L * |y(x + hξ) - y(x)| dξ           [Lipschitz f]
  ≤ h * ∫_{-i}^0 L * h * (-ξ) * M dξ                 [sub-lemma A]
  = h² * L * M * ∫_{-i}^0 (-ξ) dξ
  = h² * L * M * [ξ²/2]_{-i}^0 evaluated with sign care
  = h² * L * M * (i²/2)
  = (1/2) * i² * h² * L * M.
```

The integration `∫_{-i}^0 (-ξ) dξ = i²/2` is the only quantitative
calculation — it is `integral_id` (Mathlib,
`SpecialFunctions/Integrals/Basic.lean:200`), with sign flips:
```
∫ ξ in (-i)..0, -ξ = -∫ ξ in (-i)..0, ξ = -((0² - (-i)²)/2) = i²/2.
```

#### Lean tactic plan

This sub-lemma is the chain rule of A + B + Lipschitz, so it cannot
close until A and B are proved. After they're proved, the structure
is:

```lean
lemma residual_bound
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_diff : Differentiable ℝ y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (i : ℕ) (x h : ℝ) (hh : 0 ≤ h) :
    |y x - y (x - (i : ℝ) * h) - ((i : ℝ) * h) * deriv y x|
      ≤ (1/2) * (i : ℝ)^2 * h^2 * L * M_bound := by
  rw [residual_integral_form hy_diff hy_ode i x h hh]
  rw [abs_mul, abs_of_nonneg hh]
  -- Bound by integrating the bound from sub-lemma A.
  apply mul_le_mul_of_nonneg_left _ hh
  calc |∫ ξ in (-(i:ℝ))..0, (f (y (x + h*ξ)) - f (y x))|
      ≤ ∫ ξ in (-(i:ℝ))..0, |f (y (x + h*ξ)) - f (y x)| := by
        exact intervalIntegral.abs_integral_le_integral_abs (by linarith [Nat.cast_nonneg i])
    _ ≤ ∫ ξ in (-(i:ℝ))..0, L * |y (x + h*ξ) - y x| := by
        apply intervalIntegral.integral_mono_on (by linarith [Nat.cast_nonneg i]) ?_ ?_
        · intro ξ hξ
          -- Apply Lipschitz: |f(y(x+hξ)) - f(y x)| ≤ L * |y(x+hξ) - y x|
          have := hf_lip.dist_le_mul (y (x + h * ξ)) (y x)
          simpa [Real.dist_eq, ← NNReal.coe_le_coe, NNReal.coe_mul,
                 Real.coe_toNNReal _ hL] using this
        · sorry  -- integrability of both sides
        · sorry
    _ ≤ ∫ ξ in (-(i:ℝ))..0, L * (h * (-ξ) * M_bound) := by
        apply intervalIntegral.integral_mono_on (by linarith [Nat.cast_nonneg i]) ?_ ?_ ?_
        · intro ξ hξ
          apply mul_le_mul_of_nonneg_left _ hL
          exact exact_solution_norm_bound hM hy_diff hy_ode hf_y_bound x h hh ξ hξ.2
        · sorry  -- integrability
        · sorry
    _ = (1/2) * (i:ℝ)^2 * h * L * M_bound := by
        -- ∫ ξ in (-i)..0, L * (h * (-ξ) * M_bound) = L * h * M * ∫(-ξ) = L*h*M*i²/2.
        rw [show (fun ξ => L * (h * (-ξ) * M_bound)) = fun ξ => -(L * h * M_bound) * ξ from
              by funext; ring]
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_id]
        ring
  -- final ring: h * ((1/2) * i^2 * h * L * M) = (1/2) * i^2 * h^2 * L * M.
  -- (handled by the calc's final step + the outer `mul_le_mul_of_nonneg_left`)
```

The key Mathlib lemmas:

| Goal | Lemma |
|---|---|
| `|∫| ≤ ∫|·|` | `intervalIntegral.abs_integral_le_integral_abs` |
| Monotone integral | `intervalIntegral.integral_mono_on` |
| Lipschitz application | `LipschitzWith.dist_le_mul` (then bridge ℝ-dist to abs) |
| `∫ ξ = (b² - a²)/2` | `intervalIntegral.integral_id` |
| Pull constant out of integral | `intervalIntegral.integral_const_mul` |

The two `sorry`s are integrability obligations. `intervalIntegral.integral_mono_on`
requires both sides to be integrable on `[-(i:ℝ), 0]`. The integrand
`L * |y(x + hξ) - y x|` is continuous (composition of continuous y
with subtraction and abs); the bound `L * (h * (-ξ) * M_bound)` is a
polynomial. Both are easy `Continuous.intervalIntegrable` calls.
(Worker should write a `have h_int₁ : IntervalIntegrable …` once and
reuse it.)

#### Aristotle suitability

Sub-lemma C is *mechanical chain* (A + B + Lipschitz + `integral_id`)
once A and B are landed. Aristotle's odds rise sharply if A and B
have already returned. **Recommend: do not submit C standalone again
to Aristotle until A and B are landed**, since the standalone C
proof has to re-discover A and B from scratch.

---

### D.4 — Sub-lemma D `deriv_diff_bound`

Goal:
```
|deriv y x - deriv y (x - i*h)| ≤ (i:ℝ) * h * L * M_bound
```

#### Mathematical argument

Most tractable of the four. By `hy_ode`,
`deriv y t = f (y t)`, so
```
|deriv y x − deriv y (x − ih)|
  = |f(y(x)) − f(y(x − ih))|
  ≤ L * |y(x) − y(x − ih)|             [Lipschitz f]
  ≤ L * (h * i * M_bound)              [sub-lemma A with ξ = -i]
  = i * h * L * M_bound.
```

#### Lean tactic plan

```lean
lemma deriv_diff_bound
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_diff : Differentiable ℝ y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (i : ℕ) (x h : ℝ) (hh : 0 ≤ h) :
    |deriv y x - deriv y (x - (i : ℝ) * h)|
      ≤ (i : ℝ) * h * L * M_bound := by
  rw [hy_ode x, hy_ode (x - (i : ℝ) * h)]
  -- Goal: |f (y x) - f (y (x - i*h))| ≤ i * h * L * M_bound
  have hLip : |f (y x) - f (y (x - (i : ℝ) * h))|
                ≤ L * |y x - y (x - (i : ℝ) * h)| := by
    have := hf_lip.dist_le_mul (y x) (y (x - (i : ℝ) * h))
    -- Convert from `dist (f a) (f b) ≤ ↑K * dist a b` to abs form.
    simpa [Real.dist_eq, ← NNReal.coe_le_coe, NNReal.coe_mul,
           Real.coe_toNNReal _ hL] using this
  -- |y x - y (x - i*h)| = |y (x + h * (-i)) - y x| under x = x, ξ = -i.
  have hA : |y x - y (x - (i : ℝ) * h)| ≤ h * (i : ℝ) * M_bound := by
    have hA_raw := exact_solution_norm_bound hM hy_diff hy_ode hf_y_bound
                     x h hh (-(i : ℝ)) (neg_nonpos_of_nonneg (Nat.cast_nonneg i))
    -- hA_raw : |y (x + h * (-i)) - y x| ≤ h * (-(-i)) * M_bound
    --        = |y (x - i*h) - y x| ≤ h * i * M_bound
    have heq1 : x + h * (-(i : ℝ)) = x - (i : ℝ) * h := by ring
    have heq2 : -(-(i : ℝ)) = (i : ℝ) := by ring
    rw [heq1, heq2] at hA_raw
    rw [abs_sub_comm]
    exact hA_raw
  calc |f (y x) - f (y (x - (i : ℝ) * h))|
      ≤ L * |y x - y (x - (i : ℝ) * h)| := hLip
    _ ≤ L * (h * (i : ℝ) * M_bound) := by
        apply mul_le_mul_of_nonneg_left hA hL
    _ = (i : ℝ) * h * L * M_bound := by ring
```

#### Aristotle suitability

**Highest** of the four. Pure Lipschitz + cite-sub-lemma-A. Should
close in ≤ 5 minutes of Aristotle compute. **Recommend: if
Aristotle 4% has not budged after 1 h, give up on this round and
prove D manually as the cycle 041 deliverable.** It is ~25 lines and
only depends on sub-lemma A — so even with A still as a `sorry`, D
compiles.

---

### D.5 — Main theorem `localTruncationError_bound`

Goal:
```
|M.localTruncationError y x h|
  ≤ ((1/2) * Σ (i.val+1)² * |M.α i.succ| + Σ (i.val+1) * |M.β i.succ|)
    * L * M_bound * h²
```

#### Mathematical argument

```
|L|
  = |Σ α_{i+1} (y(x) − y(x−(i+1)h) − (i+1)h y'(x))
     + h Σ β_{i+1} (y'(x) − y'(x−(i+1)h))|     [decomposition E]
  ≤ Σ |α_{i+1}| · |y(x) − y(x−(i+1)h) − (i+1)h y'(x)|   [|sum| ≤ sum |·|]
     + h · Σ |β_{i+1}| · |y'(x) − y'(x−(i+1)h)|
  ≤ Σ |α_{i+1}| · (1/2)(i+1)² h² L M       [sub-lemma C with i ↦ i+1]
     + h · Σ |β_{i+1}| · (i+1) h L M       [sub-lemma D with i ↦ i+1]
  = (1/2) Σ |α_{i+1}| (i+1)² h² L M + Σ |β_{i+1}| (i+1) h² L M
  = ((1/2) Σ (i+1)² |α_{i+1}| + Σ (i+1) |β_{i+1}|) h² L M.
```

#### Lean tactic plan

```lean
theorem LinearMultistepMethod.localTruncationError_bound …
    : … := by
  rw [M.localTruncationError_decomposition hcons y x h]
  -- Goal: |Σ α (... residual ...) + h Σ β (... deriv-diff ...)| ≤ ...
  refine (abs_add _ _).trans ?_
  refine add_le_add ?_ ?_
  · -- Bound the α-sum
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    refine (mul_le_mul_of_nonneg_left
      (residual_bound hL hM hf_lip hy_diff hy_ode hf_y_bound (i.val + 1) x h hh)
      (abs_nonneg _)).trans ?_
    -- Goal: |M.α i.succ| * ((1/2) (i+1)² h² L M) ≤ (1/2)(i+1)²|M.α i.succ| L M h²
    ring_nf
    rfl
  · rw [abs_mul, abs_of_nonneg hh]
    refine mul_le_mul_of_nonneg_left ?_ hh
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    refine (mul_le_mul_of_nonneg_left
      (deriv_diff_bound hL hM hf_lip hy_diff hy_ode hf_y_bound (i.val + 1) x h hh)
      (abs_nonneg _)).trans ?_
    -- Goal: |M.β i.succ| * ((i+1) h L M) ≤ (i+1) |M.β i.succ| L M h
    ring_nf
    rfl
  -- Final algebraic combination — `ring_nf` handles factoring out h².
  -- One source of trouble: the LHS structure is
  --   |α-sum| + h·|β-sum| ≤ A·h² + h·B·h = A·h² + B·h²
  -- and the RHS is (A + B)·h². Use `ring_nf` to reconcile.
```

The `ring_nf` calls may need fine-tuning. The critical observation
is that `h · ((i+1) · h · L · M) = (i+1) · h² · L · M`, so the
β-sum side picks up the missing `h` to match the α-sum side's `h²`.

A cleaner alternative (per CLAUDE.md "decompose further if needed"):
factor out two helper lemmas
* `α_sum_bound` for the first big sum
* `β_sum_bound` for the second big sum
and then close the main theorem via `add_le_add` + `ring`. This
avoids any single goal blowing up `maxHeartbeats`.

#### Mathlib lemmas

| Goal | Lemma |
|---|---|
| Triangle inequality | `abs_add` |
| `\|Σ\| ≤ Σ \|·\|` | `Finset.abs_sum_le_sum_abs` |
| Monotone sum | `Finset.sum_le_sum` |
| `\|a · b\| = \|a\| · \|b\|` | `abs_mul` |
| `mul_le_mul_of_nonneg_left` | std |

#### Aristotle suitability

Low — this is integration not premise selection, and the goal is
algebraically large. **Worker should prove this manually** once
A/B/C/D land. Estimated ~50 lines including the two helper
sub-lemmas.

---

## E. Cycle 041 strategy recommendation

**Primary plan:**
1. (5 min) Run `mcp__aristotle__get_status` once. If proofs returned
   for any of A/B/C/D, copy-paste them in (verify each against
   axioms after).
2. (45 min) Manually prove **sub-lemma D** (the easiest and the only
   one whose proof depends only on sub-lemma A — and even then, only
   uses A's *statement*, not its proof).
3. (45 min) Manually prove **sub-lemma A** with the proposed
   strengthening `(hy_C1 : Continuous (deriv y))` (or upgrade
   `hy_diff` to `ContDiff ℝ 1 y`). **Faithfulness flag**: this
   strengthening is OK because Butcher's "exact solution" of
   `y' = f∘y` with Lipschitz `f` is automatically `C¹`; we are just
   surfacing what was implicit. Document in the docstring + faithfulness
   check.

If both close cleanly: cycle 041 result is "structure + 3
sub-lemmas closed (D, E, A); B/C and main remain". This satisfies
the cycle 040 strategy's "structure + 2 sub-lemmas closed" target
with margin.

**Fallback plan** (if A's continuity gap proves too sticky):
1. Prove only sub-lemma D, leave A as `sorry`. Cycle 041 result:
   "structure + 2 sub-lemmas closed (D, E); A/B/C/main remain".
2. File a follow-up issue documenting the `Continuous (deriv y)`
   gap, recommending the `ContDiff ℝ 1 y` upgrade for cycle 042.

**Cycles 042 / 043:**
* Cycle 042: prove sub-lemma B (the FTC + change of variables —
  this is the most plumbing-heavy and benefits from a fresh attempt
  once A is landed).
* Cycle 043: prove sub-lemma C (mechanical, A+B+Lipschitz) and the
  main theorem (~50 lines integrating the four). Land
  `lem:406B` complete.

This gets `lem:406B` closed in 4 cycles total (040 + 041 + 042 +
043), matching the cycle 040 task results' "2–3 more cycles"
estimate (with one extra cycle of buffer).

After `lem:406B`, the natural chain is:
* `thm:406C` (global error bound) — direct consumer.
* `thm:243A` (the cross-chapter Ch.2→Ch.4 deferral) — unblocks once
  `thm:406C` lands.

---

## F. What NOT to do this cycle

* Do **NOT** treat the prompt's "git commit/push failure" framing as
  a real problem. It is the same `attempts.md` propagation phantom
  diagnosed in cycles 008, 014, 015. Verification commands in §A
  above; if they pass (they do), proceed with the actual proof work.
* Do **NOT** revert the `β_i` decomposition to Butcher's
  `(iα_i − β_i)` form. The algebra in §B above (independent
  re-derivation, plus explicit Euler counter-example) confirms the
  worker's diagnosis. Stick with the corrected form.
* Do **NOT** raise `maxHeartbeats` above 200000. If the main
  theorem's `ring_nf` is slow, decompose into the two helper
  sub-lemmas (`α_sum_bound`, `β_sum_bound`) per §D.5.
* Do **NOT** introduce `axiom`/`constant` to bypass the
  `Continuous (deriv y)` gap. The right move is to strengthen the
  hypothesis to `ContDiff ℝ 1 y` (or `Continuous (deriv y)`), which
  is faithful to the textbook's implicit assumption.
* Do **NOT** poll Aristotle more than once in cycle 041. CLAUDE.md
  is explicit on this; the cycle 040 worker followed it correctly,
  and the cycle 041 worker should too.
* Do **NOT** edit `scripts/autonomous_loop.py` from the worker. The
  prompt-builder phantom is loop-maintainer territory; see the
  standing
  `tautology_scanner_false_positives.md` issue from cycle 015 for
  the canonical recommendation.
* Do **NOT** generalise `localTruncationError` to vector-valued
  `y : ℝ → ℝ^N` to "make the proof cleaner". The cycle 040 strategy
  was explicit: stay scalar. The proof above all works in the
  scalar case.
* Do **NOT** rewrite sub-lemma E. It is already proved manually with
  a clean ~30-line proof (`Section404.lean:588–666`), and its
  Aristotle attempt would only duplicate work. Keep the manual proof.

---

## G. Cross-references

* `.prover-state/issues/lem_406B_textbook_check.md` — cycle 040
  worker's algebraic verification of the Butcher typo. Independently
  re-derived in §B above.
* `.prover-state/issues/consultant_advice_cycle_009.md` §A —
  diagnosis of the cycle-008 "commits not reaching repo" phantom.
* `.prover-state/issues/consultant_advice_cycle_014.md` §A, §D —
  scanner false-positive pattern.
* `.prover-state/issues/consultant_advice_cycle_015.md` §B —
  cycle-015 phantom, identical pattern to cycle 040's.
* `.prover-state/issues/tautology_scanner_false_positives.md` —
  standing issue for the loop-maintainer prompt-builder bug.
* `.prover-state/task_results/cycle_040.md` — worker's cycle 040
  result document.
* `OpenMath/Chapter4/Section404.lean:516–692` — the sorry-first
  scaffold under discussion.
* `extraction/formalization_data/entities/lem_406B.json` — textbook
  statement for `lem:406B`.

---

## H. Quick-reference table — Mathlib lemmas cited above

| Goal | Lemma | File |
|---|---|---|
| FTC: `∫ y' = y(b) − y(a)` | `intervalIntegral.integral_eq_sub_of_hasDerivAt` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean` |
| Norm bound on signed integral | `intervalIntegral.norm_integral_le_of_norm_le_const` | `Basic.lean:737` |
| Affine change of variables | `intervalIntegral.smul_integral_comp_mul_add` | `Basic.lean:909` |
| Constant integral | `intervalIntegral.integral_const` | `Basic.lean:802` |
| `\|∫\| ≤ ∫\|·\|` | `intervalIntegral.abs_integral_le_integral_abs` | `Basic.lean:1276` |
| Monotone integral | `intervalIntegral.integral_mono_on` | std |
| Difference of integrals | `intervalIntegral.integral_sub` | std |
| Pull const out of integral | `intervalIntegral.integral_const_mul` | std |
| `∫ ξ = (b² − a²)/2` | `intervalIntegral.integral_id` | `SpecialFunctions/Integrals/Basic.lean:200` |
| Lipschitz application | `LipschitzWith.dist_le_mul` | `Topology/MetricSpace/Lipschitz.lean:50` |
| `\|Σ\| ≤ Σ \|·\|` | `Finset.abs_sum_le_sum_abs` | `Algebra/Order/BigOperators/Group/Finset.lean:283` |
| Triangle inequality | `abs_add` | std |
| Continuous → IntervalIntegrable | `Continuous.intervalIntegrable` | std |
| `\|h · ξ\| = h · (−ξ)` for `h ≥ 0, ξ ≤ 0` | `abs_mul` + `abs_of_nonneg` + `abs_of_nonpos` | std |

Names are best-effort accurate as of `Mathlib v4.28.0`. The worker
should verify each name with `lean_local_search` (or `lean_loogle`
on the type pattern) before committing the proof.
