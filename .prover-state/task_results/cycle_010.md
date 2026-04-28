# Cycle 010 Results

## Worked on
`thm:112B` — *one-sided Lipschitz solution-difference bound* (Butcher §112,
p. 47), formalized as
`OpenMath.Chapter1.Section112.one_sided_lipschitz_solution_diff_bound` in
`OpenMath/Chapter1/Section112.lean`.

## Approach
Followed the Cycle 010 strategy verbatim. Wrote the full proof structure
in a single pass (sorry-first, but every `sorry` filled inline as the
decomposition was written) and the file compiled on the first build.

The proof follows Butcher's six-step argument:

1. Set `g(x) := ‖y x − z x‖²` and rewrite to inner-product form
   `g x = ⟪y x − z x, y x − z x⟫` using `real_inner_self_eq_norm_sq`.
2. Compute the right derivative of `g` at every `x ∈ [x₀, b)` using
   `HasDerivWithinAt.inner (𝕜 := ℝ)` applied to the difference of the two
   solutions, then symmetrize the two summands via `real_inner_comm` to
   obtain `g'(x) = 2 ⟪f x (y x) − f x (z x), y x − z x⟫`.
3. Bound the inner product by `ℓ * g x` via the
   `OneSidedLipschitzInSecond` hypothesis (`def:112A`).
4. Apply scalar Grönwall
   (`le_gronwallBound_of_liminf_deriv_right_le`) with `δ = g x₀`,
   `K = 2ℓ`, `ε = 0`. The right-liminf hypothesis discharges via
   `HasDerivWithinAt.liminf_right_slope_le`.
5. Simplify with `gronwallBound_ε0` to
   `g x ≤ g x₀ * exp(2ℓ(x − x₀))`.
6. Take square roots: `Real.sqrt_le_sqrt` for monotonicity,
   `Real.sqrt_mul` to factor, `Real.sqrt_mul_self` to undo `‖·‖²`,
   and `Real.exp_half` (the actually-existing form
   `exp (x/2) = √(exp x)`) to halve the exponent.

## Result
**SUCCESS** — the proof closes in one shot with only standard
axioms: `#print axioms one_sided_lipschitz_solution_diff_bound` reports
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

`lake env lean OpenMath/Chapter1/Section112.lean` compiles silently;
`lake build` succeeds (2815/2815 jobs).

Aristotle was **not** used this cycle: there were no remaining
`sorry`s to submit. The strategy mandates Aristotle for sorry-first
decompositions where steps remain open after manual exploration; with
the entire proof closed in the first compile pass, submitting empty
work would have been wasted compute.

## Faithfulness check

For the one new `theorem` introduced this cycle:

- **Entity ID**: `thm:112B`
- **Textbook statement** (`statement_latex` from
  `extraction/formalization_data/entities/thm_112B.json`):
  > If $f$ satisfies a one-sided Lipschitz condition with constant $l$,
  > and $y$ and $z$ are each solutions of $y'(x) = f(x, y(x))$, then for
  > all $x \geq x_0$,
  > $\| y(x) - z(x) \| \leq \exp(l(x - x_0)) \| y(x_0) - z(x_0) \|.$
- **Lean statement**:
  ```lean
  theorem one_sided_lipschitz_solution_diff_bound
      {x₀ b : ℝ} {ℓ : ℝ} {f : ℝ → E → E}
      (hf : OneSidedLipschitzInSecond (Icc x₀ b) ℓ f)
      {y z : ℝ → E}
      (hy_cont : ContinuousOn y (Icc x₀ b))
      (hy : ∀ x ∈ Ico x₀ b, HasDerivWithinAt y (f x (y x)) (Ici x) x)
      (hz_cont : ContinuousOn z (Icc x₀ b))
      (hz : ∀ x ∈ Ico x₀ b, HasDerivWithinAt z (f x (z x)) (Ici x) x) :
      ∀ x ∈ Icc x₀ b,
        ‖y x - z x‖ ≤ Real.exp (ℓ * (x - x₀)) * ‖y x₀ - z x₀‖
  ```
- **Lean statement captures**: same content with two minor faithfulness
  flags (both documented in the theorem docstring):
  1. The textbook's "for all $x \geq x_0$" is restricted to `[x₀, b]`
     (a closed interval `Icc x₀ b`). This is a **scope restriction**
     that matches Mathlib's right-derivative API
     (`HasDerivWithinAt _ _ (Ici x) x` and Grönwall on `[a, b]`); the
     textbook hypothesis on the full ray $[x_0, \infty)$ is recovered
     by quantifying over arbitrary `b ≥ x`.
  2. The factor order is `exp(...) * ‖y x₀ - z x₀‖`, whereas the
     textbook prints `‖y(x₀) - z(x₀)‖ exp(...)`. Mathematically
     identical (real multiplication is commutative). Order chosen to
     match `gronwallBound_ε0`'s output shape.

  Continuity hypotheses `hy_cont` and `hz_cont` are technically derivable
  from `hy` and `hz` (a right-differentiable function on `[x₀, b]` is
  continuous on `[x₀, b]`), but exposing them explicitly matches the
  hypothesis shape of `ode_solution_unique` in `Section110.lean` and
  removes a one-line internal lemma without weakening the textbook claim.

### Pre-commit checklist
- [x] **Tautology check**: conclusion
      `‖y x - z x‖ ≤ exp(ℓ(x-x₀)) * ‖y x₀ - z x₀‖` is not a hypothesis.
- [x] **Identity check**: proof is a multi-step Grönwall argument, not
      `exact h` or a one-line wrapper.
- [x] **Definition smuggling**: no new `def`/`structure`/`class` this
      cycle. `OneSidedLipschitzInSecond` was unchanged from cycle 009.
- [x] **Hypothesis strength**: hypotheses match Butcher; the
      `ContinuousOn` and interval shape are minor conveniences for
      Mathlib's API and are documented in the docstring.
- [x] **Absent theorem**: theorem
      `OpenMath.Chapter1.Section112.one_sided_lipschitz_solution_diff_bound`
      exists and is fully proved.
- [x] **`#print axioms`** reports only `propext`, `Classical.choice`,
      `Quot.sound`.

## Dead ends
None this cycle. The proof closed on the first compile attempt.

## Discovery

* **`HasDerivWithinAt.inner` requires the field `𝕜` explicitly**.
  Calling `(hf.inner hg)` does not unify; one has to write
  `HasDerivWithinAt.inner (𝕜 := ℝ) hf hg` (or `(hf.inner ℝ hg)` once
  the dot-notation pulls the field through). The signature in
  `Mathlib/Analysis/InnerProductSpace/Calculus.lean:104` has
  `{f g : ℝ → E} {f' g' : E}` implicit but the field 𝕜 surfaces
  through the inner product type. Worth recording for future cycles.

* **The Mathlib name for `√(exp t) = exp (t/2)` is `Real.exp_half`**
  (stated in the form `exp (x / 2) = √(exp x)`), located in
  `Mathlib/Analysis/SpecialFunctions/Exp.lean:204`. There is **no**
  `Real.sqrt_exp` lemma despite the strategy doc's tentative name.
  Use `← Real.exp_half` plus `ring_nf` on the exponent to convert
  `√(exp(2ℓ(x-x₀)))` into `exp(ℓ(x-x₀))`.

* **`HasDerivWithinAt.liminf_right_slope_le`** in
  `Mathlib/Analysis/Calculus/Deriv/Slope.lean:236` directly converts
  `HasDerivWithinAt f f' (Ici x) x` to the Grönwall input shape
  `∀ r, f' < r → ∃ᶠ z in 𝓝[>] x, slope f x z < r`, and
  `slope f x z = (z - x)⁻¹ * (f z - f x)` for ℝ-valued `f` definitionally,
  so no extra unfolding step is required.

* **Continuity of `g(x) := ‖y x - z x‖²`** discharges as
  `(hy_cont.sub hz_cont).norm.pow 2`, three short dot-applications.

## Suggested next approach

* `thm:112B` is the last theorem in §112 outside of the qualitative
  stiffness commentary in the textbook. The natural next §1 target is
  whichever §1 theorem is next in `extraction/formalization_data/topo_order.json`
  that is still `unformalized`. Likely candidates: §113 (general linear
  methods preliminaries) or carrying on Chapter 2 if §1 is exhausted.
* Status snapshot for cycle 011 planner: `def:110A`, `lem:110B`,
  `thm:110C`, `thm:111A`, `def:112A`, `thm:112B`, `thm:123A`, `thm:123B`
  in Chapter 1 are all `formalized`. `thm:142D` is partially formalized
  but blocked on Jordan canonical form (see
  `.prover-state/issues/jordan_canonical_form_missing.md`).
* The `picard_lindelof_bound_strengthening.md` issue still applies to
  `lem:319A`. `thm:112B` was removed from its "Affected downstream
  theorems" list as part of this cycle's bookkeeping.
* The discoveries above (especially `Real.exp_half` and the explicit
  `𝕜 := ℝ` for `HasDerivWithinAt.inner`) are worth surfacing in the
  prover-state so future cycles can reuse them quickly.
