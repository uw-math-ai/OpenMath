# Cycle 042 Strategy

## Context

Cycle 041 closed sub-lemmas A (`exact_solution_norm_bound`) and D
(`deriv_diff_bound`) of `lem:406B`, with the
`Differentiable ℝ y → ContDiff ℝ 1 y` hypothesis upgrade applied to
all five sub-lemma signatures (A, B, C, D, main). Sub-lemma E
(decomposition) was already closed in cycle 040.

**Open sorries in `OpenMath/Chapter4/Section404.lean`** (verify with
`grep -n 'sorry' OpenMath/Chapter4/Section404.lean`):

1. Line 589 — `residual_integral_form` (sub-lemma B). FTC + change
   of variables.
2. Line 607 — `residual_bound` (sub-lemma C). Combines A + B + Lipschitz.
3. Line 762 — `localTruncationError_bound` (main `lem:406B`).

## Aristotle status

Project `53d674e4-20e3-43e8-9600-0b189c62c8f5` was last seen at 4 %
(`IN_PROGRESS`) at the close of cycle 041. **Poll once at the start
of this cycle** (`mcp__aristotle__get_status`) to see whether
proofs have been returned for any of A/B/C/D/E. Per CLAUDE.md, **do
not poll a second time** within this cycle. If proofs are returned:

- For A or D: compare against the manual cycle-041 proofs. The
  manual proofs are clean and short; only replace if Aristotle's
  version is meaningfully shorter or surfaces Mathlib lemmas we
  should be aware of for B/C.
- For E: keep the manual cycle-040 proof (it is already proved).
- For **B**: **prefer the Aristotle proof if it compiles** — B is
  the trickiest plumbing in the chain (FTC + affine change of
  variables) and Aristotle's premise selection often finds the
  right Mathlib lemma name faster than manual hover-info searches.
- For C: combine A + B + Lipschitz, depends on B closing first.

After the single poll, **proceed regardless** with manual proof
work on sub-lemma B (do not block on Aristotle).

## Primary target: close sub-lemma B (`residual_integral_form`)

**Goal** (`Section404.lean:582–589`):
```
y x - y (x - i*h) - (i*h) * deriv y x
  = h * ∫ ξ in (-(i:ℝ))..0, (f (y (x + h*ξ)) - f (y x))
```
under `hy_C1 : ContDiff ℝ 1 y`, `hy_ode : ∀ t, deriv y t = f (y t)`,
`hh : 0 ≤ h`.

### Math

Two FTC applications + one affine change of variables:

1. **FTC**: `y x - y (x - i*h) = ∫ t in (x - i*h)..x, deriv y t
                              = ∫ t in (x - i*h)..x, f (y t) dt`.
2. **Affine substitution** `t = x + h*ξ`: as `ξ ∈ [-i, 0]`,
   `t ∈ [x - i*h, x]`. So
   `∫ t in (x - i*h)..x, f (y t) dt = h * ∫ ξ in (-i)..0, f(y(x + h*ξ)) dξ`.
3. **Constant integral**: `(i*h) * deriv y x = (i*h) * f(y x)
                           = h * ∫ ξ in (-i)..0, f(y x) dξ`
   (since `∫ _ in (-i)..0, f(y x) = (0 - (-i)) • f(y x) = i * f(y x)`).
4. **Subtract**: result is `h * ∫_{-i}^0 [f(y(x+h*ξ)) − f(y x)] dξ`.

### Mathlib lemmas (verify each name with `lean_local_search` or
`lean_hover_info` before relying on it)

| Goal | Likely Mathlib name | Notes |
|------|--------------------|-------|
| FTC: `∫ y' = y(b) − y(a)` | `intervalIntegral.integral_eq_sub_of_hasDerivAt` | Already used in sub-lemma A. |
| Affine change of variables | `intervalIntegral.smul_integral_comp_mul_add` | `c • ∫ x in a..b, f (c*x + d) = ∫ x in c*a+d..c*b+d, f x`. With `c = h, d = x, a = -i, b = 0` we get `h * ∫ ξ in (-i)..0, f(y(h*ξ + x)) = ∫ t in (x - i*h)..x, f(y t)`. |
| Constant integral | `intervalIntegral.integral_const` | `∫ _ in a..b, c = (b - a) • c`. |
| Difference of integrals | `intervalIntegral.integral_sub` | Needs both integrands `IntervalIntegrable`. |
| Constant times integral | `intervalIntegral.integral_const_mul` | If you need `h * ∫ _ = ∫ h * _`. |

### Proof structure (template — refine via `lean_multi_attempt`)

```lean
lemma residual_integral_form … := by
  -- Setup: f∘y continuous (cf. sub-lemma A step 1).
  have hfy_cont : Continuous (fun t => f (y t)) := by
    have heq : (fun t => f (y t)) = deriv y := by
      funext t; exact (hy_ode t).symm
    rw [heq]; exact hy_C1.continuous_deriv le_rfl
  -- HasDerivAt y (f (y t)) t pointwise.
  have hderiv : ∀ t, HasDerivAt y (f (y t)) t := by
    intro t
    have ht := ((hy_C1.differentiable
                  (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) t).hasDerivAt
    rw [hy_ode t] at ht; exact ht
  -- Integrability of f∘y on any interval.
  have hint_any : ∀ a b : ℝ,
      IntervalIntegrable (fun t => f (y t)) MeasureTheory.volume a b :=
    fun a b => hfy_cont.intervalIntegrable a b

  -- Step A: FTC on [(x - i*h), x].
  have hFTC : ∫ t in (x - (i:ℝ)*h)..x, f (y t) = y x - y (x - (i:ℝ)*h) := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
              (fun t _ => hderiv t) (hint_any (x - (i:ℝ)*h) x)
    simpa using this

  -- Step B: change of variables t = x + h*ξ. Use smul_integral_comp_mul_add
  -- with c := h, d := x, a := -i, b := 0.
  have hCV : h * (∫ ξ in (-(i:ℝ))..0, f (y (h*ξ + x)))
              = ∫ t in (h*(-(i:ℝ)) + x)..(h*0 + x), f (y t) := by
    have := intervalIntegral.smul_integral_comp_mul_add
              (f := fun t => f (y t)) (a := -(i:ℝ)) (b := 0) (c := h) (d := x)
    -- API may write `c • ∫ … = ∫ …`; for ℝ smul = mul, simp it down.
    simpa [smul_eq_mul] using this
  -- Reconcile endpoint shape `h * ξ + x` ↔ `x + h * ξ`, and
  -- `h*(-i) + x = x - i*h`, `h*0 + x = x`. Use `congr 1` /
  -- `Finset.sum_congr` / direct rewrites with `add_comm`,
  -- and `show … = …; ring` if needed.

  -- Step C: constant integral  ∫ _ in (-i)..0, f(y x) = i * f(y x).
  have hConst : ∫ _ξ in (-(i:ℝ))..0, f (y x) = (i : ℝ) * f (y x) := by
    rw [intervalIntegral.integral_const]
    simp [smul_eq_mul]
    ring

  -- Step D: assemble. The RHS is
  --   h * ∫ (f(y(x + h*ξ)) - f(y x)) = h * ∫ f(y(x + h*ξ)) − h * ∫ f(y x)
  -- The first piece equals ∫ t in (x - i*h)..x, f(y t) = y x - y(x - i*h)
  -- by Steps B + A. The second piece equals h * (i * f(y x)) =
  -- (i*h) * f(y x) = (i*h) * deriv y x by Step C and hy_ode.
  rw [intervalIntegral.integral_sub
        (hfy_cont.comp_continuous_on (by fun_prop : ContinuousOn _ _) |>.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _)]
  rw [hy_ode x]
  -- … combine hFTC, hCV, hConst, then `ring` to finish.
  sorry  -- replace with assembled term
```

The `sorry` at the end is the *assembly step*; once the four
named pieces (`hfy_cont`, `hderiv`, `hFTC`, `hCV`, `hConst`) are
in place, the closure should be ≤ 10 lines of `rw`, `simp`, `ring`.
**Plan ~60–90 minutes for this.**

### Calibration checklist (do these first, before writing the proof body)

Use `lean_multi_attempt` / `lean_hover_info` at line 589 to verify:

1. The exact name of `intervalIntegral.smul_integral_comp_mul_add`.
   If not present under that name, try `loogle`:
   `intervalIntegral.smul_integral_comp_*` or `integral_comp_mul_*`.
   Common variants: `integral_comp_mul_add_left`,
   `integral_comp_smul`, `integral_comp_add_left`. Pick whichever
   aligns with the textbook substitution `t = h*ξ + x`. **Beware of
   sign conventions** for `c < 0` cases — here `c = h ≥ 0` so we are
   in the friendly case.

2. The `IntervalIntegrable` premise count for
   `intervalIntegral.integral_sub`. Newer Mathlib often uses
   `IntervalIntegrable f μ a b` for the same `a, b` on both sides
   of the subtraction.

3. The exact form of `intervalIntegral.integral_const`'s output:
   `∫ _ in a..b, c = (b - a) • c` vs `(b - a) * c` (for ℝ).

### Aristotle submission (optional, low priority)

If the manual proof of B drags past 90 min and you still don't
have a clean closure, batch-submit B + C as a fresh Aristotle job
with a short explanatory prompt naming
`smul_integral_comp_mul_add` and `integral_eq_sub_of_hasDerivAt`
explicitly. Sleep 30 min per CLAUDE.md, then check once at the end
of cycle. **Do not submit before trying the manual proof for at
least an hour** — you will save Aristotle compute and produce a
proof you actually understand.

## Stretch (only if B closes with > 1 hour remaining)

Attempt sub-lemma C (`residual_bound`) using the chain that the
cycle-040 consultant note §D.3 spelled out:

```
|residual|
  = h * |∫_{-i}^0 [f(y(x+hξ)) - f(y x)] dξ|     -- by B
  ≤ h * ∫_{-i}^0 |f(y(x+hξ)) - f(y x)| dξ        -- abs_integral_le_integral_abs
  ≤ h * ∫_{-i}^0 L * |y(x+hξ) - y x| dξ          -- Lipschitz
  ≤ h * ∫_{-i}^0 L * (h * (-ξ) * M) dξ           -- sub-lemma A
  = h² * L * M * ∫_{-i}^0 (-ξ) dξ
  = h² * L * M * (i²/2)
  = (1/2) i² h² L M.
```

Key Mathlib lemmas:
- `intervalIntegral.abs_integral_le_integral_abs`
- `intervalIntegral.integral_mono_on` (with two integrability sides)
- `intervalIntegral.integral_id` for `∫ ξ = (b² − a²)/2`
- `intervalIntegral.integral_const_mul`

The integrability obligations are the main fiddle factor; both
integrands are continuous, so `Continuous.intervalIntegrable` clears
them, but you'll need to thread the continuity proofs through.

**Do not start C before B is fully closed.** C cannot compile
without B's statement, and partial C work is wasted effort if B's
final form needs adjustment.

## Do NOT this cycle

- **Do NOT** start sub-lemma C, the main `lem:406B` theorem, or
  any §405/§406 follow-on entity until B is closed. The cycle's
  scope is strictly B (with C as a stretch).
- **Do NOT** revert the `ContDiff ℝ 1 y` hypothesis. Cycle 041 made
  it consistent across all five signatures; reverting wastes
  effort and breaks A and D.
- **Do NOT** revert sub-lemma E's algebraic decomposition to
  Butcher's textbook (iα_i − β_i) form. The β_i form is
  algebraically correct (independently verified in
  `consultant_advice_cycle_040.md` §B and
  `lem_406B_textbook_check.md`). Stick with it.
- **Do NOT** raise `maxHeartbeats` above 200000. If `ring` at the
  assembly step is slow, decompose the assembly into named `have`
  steps.
- **Do NOT** introduce `axiom` / `constant` for any plumbing gap.
- **Do NOT** poll Aristotle more than once this cycle. CLAUDE.md.
- **Do NOT** edit `scripts/autonomous_loop.py`. Loop maintainer
  territory; see `tautology_scanner_false_positives.md`.
- **Do NOT** trust prompt-builder "stuck" or "commits not reaching
  repo" verdicts at face value. Cycles 008/014/015/040 all had
  phantom verdicts contradicted by `git log`. Verify against HEAD
  if any such verdict appears: `git log -1 --format='%H %s'` and
  `git rev-parse origin/Main/Experiments` should match.
- **Do NOT** generalise to `y : ℝ → ℝ^N` or other vector-valued
  variants. Stay scalar; cycle-040 strategy is binding.

## Faithfulness check requirements (per CLAUDE.md)

For sub-lemma B (and C if it lands):

- **Tautology / identity / smuggling checks**: confirm B's
  conclusion is not a verbatim hypothesis (it's an integral
  equation, so this is automatic).
- **Hypothesis-strength check**: the signature already has
  `ContDiff ℝ 1 y`; this matches the textbook's implicit
  assumption (Picard–Lindelöf produces a `C¹` solution from
  Lipschitz `f`). No new hypothesis-strength concerns.
- **Absent-theorem check**: the file's `localTruncationError_bound`
  docstring promises the §406 block decomposition; sub-lemma E is
  the formal statement of that promise and is already proved. No
  new "promised but absent" gap.

Document the check in `task_results/cycle_042.md` per the standard
format (see CLAUDE.md "Task Results Format").

## Pre-commit checklist

Before `git commit`:

1. `lake env lean OpenMath/Chapter4/Section404.lean` — clean.
   Sorry count should drop from 3 → 2 (B closed) or 3 → 1 (B and
   C closed in stretch).
2. `#print axioms residual_integral_form` (and `residual_bound`
   if closed). Expected: `[propext, Classical.choice, Quot.sound]`.
3. `git diff --stat OpenMath/Chapter4/Section404.lean` shows the
   B (and possibly C) closure.
4. `task_results/cycle_042.md` written per CLAUDE.md format,
   including the faithfulness check.
5. `git log -1` and `git rev-parse origin/Main/Experiments` agree
   after `git push`.

## Suggested commit message

If B closes only:
`Cycle 042 — close sub-lemma B of lem:406B (FTC + change of variables)`

If both B and C close:
`Cycle 042 — close sub-lemmas B and C of lem:406B`

## Cross-references for the worker

- Proof sketches and Mathlib lemma table:
  `.prover-state/issues/consultant_advice_cycle_040.md` §D.2 (B),
  §D.3 (C), §H (lemma reference table).
- Algebraic verification of the textbook typo:
  `.prover-state/issues/lem_406B_textbook_check.md`.
- File: `OpenMath/Chapter4/Section404.lean:582–607` (B and C
  signatures and docstrings).
- Cycle 041 deliverables (sub-lemmas A and D) at
  `OpenMath/Chapter4/Section404.lean:526–647` for reference proof
  shape.
