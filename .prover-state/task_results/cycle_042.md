# Cycle 042 Results

## Worked on
Sub-lemmas B (`residual_integral_form`) and C (`residual_bound`) of
`lem:406B`, in `OpenMath/Chapter4/Section404.lean`.

## Approach

### Aristotle poll (single)
At the start of cycle, polled
`mcp__aristotle__get_status` for project
`53d674e4-20e3-43e8-9600-0b189c62c8f5`. Status: `IN_PROGRESS`,
`percent_complete = 4` (no advance from cycle 041's close). Per
strategy, did not poll a second time and proceeded with manual proof
work.

### Sub-lemma B (`residual_integral_form`)
Followed the planner's proof template directly: FTC + affine change
of variables + constant integral + assembly. Mathlib lemmas verified
via `lean_loogle`:

- `intervalIntegral.integral_eq_sub_of_hasDerivAt` (already used in
  sub-lemma A).
- `intervalIntegral.smul_integral_comp_mul_add` — the key change-of-
  variables lemma `c • ∫ x in a..b, f(c*x + d) = ∫ x in c*a+d..c*b+d, f x`.
  Instantiated with `c := h, d := x, a := -(i:ℝ), b := 0`.
- `intervalIntegral.integral_const` — `∫ _ in a..b, c = (b-a) • c`.
- `intervalIntegral.integral_sub` — splits the difference of
  integrands.

Setup mirrors sub-lemma A's preamble (continuity of `f∘y` from
`hy_C1.continuous_deriv` + `hy_ode`, `HasDerivAt y (f(y t)) t` from
`hy_C1.differentiable`).

The "endpoint reconciliation" step rewrites `h*(-(i:ℝ)) + x` to
`x - (i:ℝ)*h` and `h*0 + x` to `x`, plus a `funext` to flip
`f(y(h*ξ + x))` to `f(y(x + h*ξ))` via `add_comm`.

Final assembly is a five-rewrite line:
```
rw [intervalIntegral.integral_sub hfyhx_int hfyx_int]
rw [hConst, mul_sub, hCV, hFTC, hy_ode x]
ring
```

### Sub-lemma C (`residual_bound`) — stretch goal closed
Followed the planner's chain template:
1. Apply sub-lemma B to rewrite LHS into integral form.
2. Pull `h` out of the absolute value using `abs_mul` + `abs_of_nonneg hh`.
3. Apply `intervalIntegral.abs_integral_le_integral_abs` (with
   `-(i:ℝ) ≤ 0`).
4. Pointwise Lipschitz bound + `intervalIntegral.integral_mono_on`.
5. Pointwise sub-lemma A bound + a second `integral_mono_on` (this
   uses `Set.Icc` membership; with `a ≤ b`, `Set.uIcc = Set.Icc`, so
   `hξ.2` gives `ξ ≤ 0` directly).
6. Compute `∫ ξ in (-i)..0, L * (h * (-ξ) * M_bound)` via:
   - factor as `(L * h * M_bound) * (-ξ)`,
   - `intervalIntegral.integral_const_mul` to pull the constant,
   - `intervalIntegral.integral_neg` + `integral_id` (note: `integral_id`
     is *not* in the `intervalIntegral` namespace — it lives in
     `Mathlib.Analysis.SpecialFunctions.Integrals.Basic`),
   - `ring` to finish `= L * h * M_bound * (i^2/2)`.
7. Final `calc` chains the four steps and closes with `ring` to convert
   `h * (L * h * M_bound * (i^2/2))` to `(1/2) * i^2 * h^2 * L * M_bound`.

## Result
**SUCCESS** — both sub-lemmas B and C closed.

- `OpenMath/Chapter4/Section404.lean` builds clean
  (`lake build OpenMath.Chapter4.Section404` → `Build completed
  successfully`).
- Sorry count dropped 3 → 1. The single remaining sorry is the main
  `LinearMultistepMethod.localTruncationError_bound` at line 882,
  which is the §406 cycle's terminal target.
- Axiom check (`#print axioms` after rebuild):
  - `residual_integral_form`: `[propext, Classical.choice, Quot.sound]`
  - `residual_bound`: `[propext, Classical.choice, Quot.sound]`
  - (No `sorryAx`. Cycle 041's `exact_solution_norm_bound`, `deriv_diff_bound`, and
    `localTruncationError_decomposition` remain clean as well.)

## Faithfulness check

### `residual_integral_form` (sub-lemma B of `lem:406B`)
- Entity ID: helper sub-lemma of `lem:406B` (ID `lem:406B`,
  `entities/lem_406B.json`).
- Textbook statement (quoted from `proof_latex`, step 1):
  > "y(x) − y(x − ih) − hiy'(x) = h ∫_{−i}^{0} (f(y(x + hξ)) − f(y(x))) dξ"
- Lean statement captures: **same content** (modulo Lean syntax).
  Hypotheses are `ContDiff ℝ 1 y` (textbook implicit: y is C¹ from
  Picard–Lindelöf with Lipschitz f), `∀ t, deriv y t = f (y t)`
  (the ODE), `0 ≤ h` (kept for signature parity with A/C/D/main; not
  required for the integral identity itself — the unused `hh`
  warning reflects that, and the planner explicitly sanctioned the
  parity).
- Tautology / identity / smuggling: clean (multi-rewrite proof
  using FTC + change-of-variables; conclusion is an integral
  equation, hypotheses are differentiability).
- Hypothesis strength: matches textbook exactly. The textbook proof
  silently assumes y is C¹; we surface that explicitly and document
  in the existing `§406` block header.

### `residual_bound` (sub-lemma C of `lem:406B`)
- Entity ID: helper sub-lemma of `lem:406B`.
- Textbook statement (quoted from `proof_latex`, step 4):
  > "‖y(x) − y(x − ih) − ihy'(x)‖ ≤ (1/2) i² h² LM"
- Lean statement captures: **same content**. Hypotheses
  `0 ≤ L, 0 ≤ M_bound, LipschitzWith L.toNNReal f, ContDiff ℝ 1 y,
  ∀ t, deriv y t = f (y t), ∀ t, |f (y t)| ≤ M_bound, 0 ≤ h`
  match the textbook's implicit assumptions for this step.
- Tautology / identity / smuggling: clean (calc chain through three
  integral inequalities + a closed-form computation of `∫(-ξ)`).
- Hypothesis strength: textbook-faithful. `0 ≤ h` is genuinely
  needed here (used in `abs_of_nonneg hh`), so not redundant.

## Dead ends
None this cycle. Both proofs landed on the first compile after
checking lemma signatures with `lean_loogle` / `lean_leansearch`.

A near-miss: my first instinct was to look for `intervalIntegral.integral_id`,
but it lives at top level (`integral_id` from
`Mathlib.Analysis.SpecialFunctions.Integrals.Basic`), not in the
`intervalIntegral` namespace. `lean_loogle` returned no result for
the namespaced version; `lean_leansearch` for "interval integral of
x equals (b² - a²)/2" found it at the top level.

## Discovery

1. **`integral_id` is top-level, not namespaced.** Worth remembering
   for any future cycle that needs `∫ x = (b² - a²)/2`.
2. **`Set.uIcc = Set.Icc` when `a ≤ b`.** `intervalIntegral.integral_mono_on`'s
   hypothesis is `∀ x ∈ Set.Icc a b, f x ≤ g x` (not `Set.uIcc`); when
   the side condition `a ≤ b` is supplied to `integral_mono_on`,
   `hξ.2` directly yields the upper-bound information needed for
   pointwise application of sub-lemma A.
3. **`olean` cache lag matters for `#print axioms`.**
   `lake env lean` on the source file reports diagnostics live, but
   a separate file using `#print axioms` reads the cached `.olean`,
   which can be stale relative to recent edits. Always `lake build`
   the target module before believing an `#print axioms` report.
4. **`smul_integral_comp_mul_add`'s body shape.** The substitution
   produces `f (c * x + d)` (multiplicative term first), not
   `f (d + c * x)`. Reconciliation with the textbook form
   `f(y(x + h*ξ))` needs a `funext` + `add_comm`, not just `ring`,
   because the integrand is wrapped in a `fun ξ => …`.

## Suggested next approach

The terminal target is the main `lem:406B`
(`LinearMultistepMethod.localTruncationError_bound` at line 882).
With sub-lemmas A, B, C, D, E all closed, the remaining proof is the
*algebraic assembly*:

1. Start from `localTruncationError_decomposition` (sub-lemma E) to
   write `L(y, x, h)` as
   `∑ α_{i+1} (y(x) − y(x−(i+1)h) − (i+1)h·y'(x))
     + h ∑ β_{i+1} (y'(x) − y'(x−(i+1)h))`.
2. Take absolute values and apply the triangle inequality to each
   sum (`Finset.abs_sum_le_sum_abs`).
3. Bound each `α`-term using sub-lemma C with `i := i+1`:
   `|y(x) − y(x−(i+1)h) − (i+1)h·y'(x)| ≤ (1/2) (i+1)² h² L M`.
4. Bound each `β`-term using sub-lemma D with `i := i+1`:
   `|y'(x) − y'(x−(i+1)h)| ≤ (i+1) h L M`.
5. Pull constants out of the sums, factor `L M h²` and the `1/2`,
   and arithmetic ride to the conclusion
   `((1/2) ∑ (i+1)² |α_{i+1}| + ∑ (i+1) |β_{i+1}|) L M h²`.

Mathlib lemmas to prepare for the planner:
- `Finset.abs_sum_le_sum_abs` (triangle for finite sums).
- `Finset.sum_le_sum` (monotonicity of finite sums when each term
  is bounded above).
- `abs_mul` to split `|α_{i+1} * (...)|` into `|α_{i+1}| * |(...)|`.

Estimated complexity: comparable to sub-lemma E's algebraic
manipulation (≈40 lines), with the bulk in carefully threading
absolute values through two `Finset.sum_le_sum` applications. The
cleanest structuring is probably two intermediate `have` lemmas
(one for the α-sum bound, one for the β-sum bound), then a single
closing chain.

The cycle 040 consultant note (`consultant_advice_cycle_040.md`)
already sketches this assembly in §H; cycle 043 should follow that
sketch directly.
