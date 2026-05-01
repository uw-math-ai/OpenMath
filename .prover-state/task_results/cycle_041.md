# Cycle 041 Results

## Worked on

`lem:406B` (Butcher §406, p. 346 — *Convergence condition sufficiency
bound*) — closing sub-lemmas A and D of the cycle-040 sorry-first
scaffold in `OpenMath/Chapter4/Section404.lean`.

Per the cycle-041 strategy, the cycle goal was

  "structure + 2 sub-lemmas closed" (E from cycle 040, plus D and A)

with hypothesis-strength upgrade `Differentiable ℝ y → ContDiff ℝ 1 y`
in all five `lem:406B` sub-lemma signatures (A, B, C, D, main).

## Approach

1. **Aristotle status check (one poll only, per CLAUDE.md)**.
   Project `53d674e4-20e3-43e8-9600-0b189c62c8f5` was still
   `IN_PROGRESS` at 4 % (created 2026-04-30 22:08, last update
   23:28). Per strategy, did NOT poll again — proceeded directly to
   manual proofs and noted "no Aristotle contribution this cycle".

2. **Hypothesis upgrade (sub-lemmas A–D + main)**.
   Replaced `(hy_diff : Differentiable ℝ y)` with
   `(hy_C1 : ContDiff ℝ 1 y)` in all five signatures. This is
   *required* for sub-lemma A's FTC argument (which needs `deriv y`
   continuous, not merely defined pointwise) and is consistent with
   the textbook's implicit assumption (Picard–Lindelöf produces a
   `C¹` solution; see the docstring on
   `exact_solution_norm_bound`).

3. **Sub-lemma D (`deriv_diff_bound`)** — Lipschitz-of-`f` step
   + sub-lemma A at `ξ = -i`. Closed using:
   - `LipschitzWith.dist_le_mul` + `Real.dist_eq` for the bridge
     `|f a − f b| ≤ L · |a − b|`.
   - `Real.coe_toNNReal L hL` to discharge the `↑L.toNNReal = L`
     coercion.
   - `exact_solution_norm_bound … hh (-(i:ℝ)) …` for the
     `|y x − y(x − i·h)|` bound, with two `ring` rewrites
     (`x + h*(-i) = x - i*h`, `-(-i) = i`) and `abs_sub_comm`.
   - Final `calc` chain combining the two.

4. **Sub-lemma A (`exact_solution_norm_bound`)** — FTC + integral
   norm bound. Closed using:
   - `ContDiff.continuous_deriv` (with `1 ≤ (1 : WithTop ℕ∞)`)
     to extract continuity of `deriv y`, transferred to `f∘y` via
     `hy_ode`.
   - `ContDiff.differentiable` (with proof `(1:WithTop ℕ∞) ≠ 0`)
     to get `HasDerivAt y (f (y t)) t` pointwise, again via
     `hy_ode`.
   - `Continuous.intervalIntegrable` for integrability of `f∘y`
     on `[x, x + h·ξ]`.
   - `intervalIntegral.integral_eq_sub_of_hasDerivAt` for FTC
     `∫_x^{x+h·ξ} f(y t) = y(x+h·ξ) - y x`.
   - `intervalIntegral.norm_integral_le_of_norm_le_const` for
     `|∫| ≤ M_bound * |h·ξ|`.
   - `abs_mul`, `abs_of_nonneg hh`, `abs_of_nonpos hξ` to rewrite
     `|h·ξ| = h·(-ξ)`.

## Result

**SUCCESS** — both sub-lemmas D and A close.

Verification:

```
$ lake env lean OpenMath/Chapter4/Section404.lean
warning: declaration uses `sorry`  (line 596 — sub-lemma B)
warning: declaration uses `sorry`  (line 610 — sub-lemma C)
warning: declaration uses `sorry`  (line 762 — main lem:406B)
```

Lines previously at 525 (A) and 577 (D) no longer carry `sorry`.

Axiom checks (inline `#print axioms` in file, removed before commit)
confirm both new lemmas use only `[propext, Classical.choice,
Quot.sound]`.

Open sorries remaining: B (residual_integral_form), C
(residual_bound), main (localTruncationError_bound). Cycle 042
target per strategy: sub-lemma B (FTC + change-of-variables); cycle
043: C; then main.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `exact_solution_norm_bound` (helper for `lem:406B`)

- **Entity ID**: not a textbook entity (helper). Used in the
  `lem:406B` proof at the line
  > "noting, that for ξ ≤ 0,
  > `‖y(x + hξ) − y(x)‖ ≤ h ∫_ξ^0 ‖f(x + hξ)‖ dξ ≤ h|ξ|M`"
  (Butcher §406, equation tag (406b)).
- **Lean statement captures**: same content. The textbook's
  implicit identification `f(x) = f(y(x))` (a typo — the integrand
  should be `f(y(x + hξ))` per the surrounding context) is
  resolved in the Lean statement by writing `|f(y t)| ≤ M_bound`
  pointwise.
- **Hypothesis-strength change**: `Differentiable ℝ y` →
  `ContDiff ℝ 1 y`. This is **NOT a strengthening relative to the
  textbook**: Butcher §406 implicitly applies FTC to `y'`, which
  requires `y'` continuous; Picard–Lindelöf (Butcher §110, our
  `thm:110C`) produces precisely such a `C¹` solution from
  Lipschitz `f`. Surfacing `ContDiff ℝ 1 y` makes the implicit
  assumption explicit. The docstring of `exact_solution_norm_bound`
  documents this explicitly.

### `deriv_diff_bound` (helper for `lem:406B`)

- **Entity ID**: not a textbook entity (helper). Matches the
  intermediate Butcher §406 step
  > "From (406b), we see also that
  > `‖f(y(x)) − f(y(x − ih))‖ ≤ ihLM`."
- **Lean statement captures**: same content (after rewrite via
  `hy_ode`, the goal `|deriv y x − deriv y (x − i·h)|` becomes
  `|f (y x) − f (y (x − i·h))|`).
- **Hypothesis-strength**: same `ContDiff ℝ 1 y` as A
  (signature parity). The proof itself only uses
  `hy_ode` and the *statement* of A; it does not exercise
  continuity of `deriv y` directly.

### Hypothesis-strength upgrade in B, C, main (signatures only)

The `Differentiable ℝ y → ContDiff ℝ 1 y` upgrade was propagated to
sub-lemmas B (line 600), C (line 614), and the main `lem:406B`
theorem (line 750) **even though those bodies are still `sorry`**.
This is consistent-signature hygiene per the cycle-041 fallback
plan: the cost of consistent signatures is zero even before the
proofs land.

### No tautology / identity / smuggling issues

- Tautology check: neither A nor D's conclusion appears verbatim
  in their hypotheses. ✓
- Identity check: both proofs do real mathematical work (FTC for
  A, Lipschitz-chain for D), not `exact h`. ✓
- Definition smuggling: no new `def` or `structure` introduced
  this cycle. ✓
- Hypothesis strength: `ContDiff ℝ 1 y` upgrade documented above;
  no other hypotheses are stronger than the textbook needs. ✓

## Dead ends

None this cycle. The strategy's ready-made proof sketches for A and
D translated to compiling Lean almost line-for-line. The only
deviations from the strategy's draft:

- `ContDiff.differentiable` takes `n ≠ 0`, not `1 ≤ n` (the
  draft used `le_rfl` which has the wrong type). Fixed by
  `(by norm_num : (1 : WithTop ℕ∞) ≠ 0)`.
- The strategy's `simpa [add_sub_cancel_left]` at the
  `intervalIntegral.norm_integral_le_of_norm_le_const` step did
  not need `simpa`; a direct `rw [Real.norm_eq_abs]` plus a
  manual rewrite of `(x + h*ξ) - x = h*ξ` worked cleanly.

## Discovery

1. **`ContDiff` ↔ `Differentiable + Continuous (deriv y)`**.
   `ContDiff ℝ 1 y` is the canonical Mathlib spelling for "y is
   continuously differentiable". It gives both `Differentiable`
   (via `ContDiff.differentiable` with `1 ≠ 0`) and `Continuous
   (deriv y)` (via `ContDiff.continuous_deriv` with `1 ≤ 1`). For
   ODE arguments that require FTC, this is the right hypothesis
   level — `Differentiable` alone is insufficient (the derivative
   need not be Riemann/Bochner integrable in general).

2. **`WithTop ℕ∞` arithmetic**. `ContDiff` takes `n : WithTop ℕ∞`,
   so `1 ≤ n` and `n ≠ 0` need `WithTop`-aware tactics. `le_rfl`
   works for `1 ≤ 1`; `by norm_num : (1 : WithTop ℕ∞) ≠ 0` works
   for `1 ≠ 0`. Saved here as a discovery for future ODE cycles.

3. **`LipschitzWith.dist_le_mul` + `Real.coe_toNNReal`**. The
   Lipschitz API gives `dist (f a) (f b) ≤ ↑K * dist a b`. To
   convert to `|f a − f b| ≤ L * |a − b|` with the original real
   `L`, use `Real.dist_eq` (twice) and `Real.coe_toNNReal L hL`
   to discharge the `↑L.toNNReal = L` coercion.

## Suggested next approach

1. **Cycle 042 — sub-lemma B (`residual_integral_form`)**. This is
   the FTC + change-of-variables step:
   ```
   y(x) − y(x − i·h) − i·h·y'(x)
     = h * ∫_{-i}^{0} (f(y(x+h·ξ)) − f(y x)) dξ
   ```
   Two FTC applications and one substitution `t = x + h·ξ` (i.e.
   `intervalIntegral.integral_comp_smul_left` or
   `integral_comp_mul_left`). The ContDiff hypothesis already
   matches A; the change-of-variables Mathlib lemma signatures need
   `lean_hover_info` calibration.

2. **Cycle 043 — sub-lemma C (`residual_bound`)**. Combines A + B
   + Lipschitz: bound `h * ∫_{-i}^{0} L * |y(x+h·ξ) − y x| dξ` by
   `(1/2) i² h² L M_bound` using A's bound and the integral
   identity `∫_{-i}^0 (-ξ) dξ = i²/2`.

3. **Cycle 044 (or 045) — main `lem:406B`**. Combine sub-lemma E
   (decomposition) with A, B, C, D bounds via `Finset.abs_sum_le`
   and term-by-term bounds.

4. **Aristotle**. Continue letting the cycle-040 submission run.
   If it returns proofs of A/B/C/D/E during cycle 042 or later,
   compare vs. the manual proofs (Aristotle proofs of A/D may be
   shorter; consider replacement).

## Checks summary

| Check | Status |
|------|--------|
| `lake env lean OpenMath/Chapter4/Section404.lean` | clean (3 expected sorrys) |
| `#print axioms exact_solution_norm_bound` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms deriv_diff_bound` | `[propext, Classical.choice, Quot.sound]` |
| Sub-lemma E re-verified untouched | yes |
| Aristotle polled exactly once | yes (project IN_PROGRESS, no contribution) |
