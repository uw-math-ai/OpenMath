# Issue: `IsConvergent` predicate strengthened beyond textbook (cycle 068)

## Faithfulness deviation

In cycle 068, the formal definition `LinearMultistepMethod.IsConvergent`
(Butcher def:402A, `OpenMath/Chapter4/Section404.lean:305`) was
strengthened to add hypotheses not present in Butcher's literal
definition. This issue documents the deviation, the reasons each
strengthening is required, and why the deviation is acceptable.

## Textbook statement (`extraction/formalization_data/entities/def_402A.json`)

> "Consider a linear multistep method used with a starting method as
> described in the previous discussion. Let `Y_m` denote the
> approximation to `y(x)` found using `m` steps with `h = (x - x_0)/m`.
> The function `f` is assumed to be continuous and to satisfy a
> Lipschitz condition in its second variable. The linear multistep
> method is said to be `convergent' if, for any such initial value
> problem,
>
>   `Y_m − y(x) → 0, as m → ∞`."
>
> (Butcher 2008, p. 340.)

The textbook hypothesises only:

* `f` continuous (jointly).
* `f` Lipschitz in its second variable.

## Lean definition (post-cycle-068, line 305)

The strengthened predicate adds:

* `LipschitzWith L (Function.uncurry f)` — joint Lipschitz on the
  uncurried `f` (rather than `LipschitzInSecond Set.univ L f`).
* `ContDiff ℝ 1 yex` — global C¹ on the exact solution.
* `(∀ t : ℝ, |f t (yex t)| ≤ M_bound)` with `0 ≤ M_bound` — a global
  trajectory bound.
* The `HasDerivAt` hypothesis is also widened from `∀ x ≥ x₀` to
  `∀ x : ℝ` (matches the global `ContDiff` shape).

## Why each strengthening is mathematically required

| Helper expects (cycles 064–067) | Textbook `IsConvergent` literal text |
|---|---|
| `LipschitzWith L_joint (Function.uncurry f)` (joint) | `LipschitzInSecond Set.univ L f` (spatial only — `∀ x, LipschitzWith L (f x)`) |
| `∀ t : ℝ, \|f t (yex t)\| ≤ M_bound` (global) | nothing — only `Continuous (Function.uncurry f)` |
| `ContDiff ℝ 1 yex` (global C¹) | only `∀ x ≥ x₀, HasDerivAt yex (f x (yex x)) x` (one-sided, partial) |

Each gap is genuine — none can be derived from the textbook's literal
hypotheses:

1. **Joint Lipschitz vs. spatial-only Lipschitz.** Continuity in `t`
   is qualitative; joint-Lipschitz is quantitative. Continuity does
   not yield any modulus that bounds `|f t₁ y₁ − f t₂ y₂|` when
   `t₁ ≠ t₂`. The cycle 065+ helper chain (e.g. `T1_bound_nonauto`,
   `T2_bound_nonauto`, `residual_bound_nonauto`) applies Lipschitz
   with *different* time arguments on each side, which spatial-only
   Lipschitz cannot bound.

2. **Global trajectory bound.** Continuity of `f` and continuity of
   `yex` only yield bounds on compact intervals, not on all of ℝ.
   The autonomous theorem template
   (`stable_consistent_isConvergent_autonomous`) takes
   `∀ t : ℝ, |f (yex t)| ≤ M_bound` as an explicit hypothesis
   precisely because it cannot be derived from continuity alone.

3. **Global C¹ on `yex`.** One-sided `HasDerivAt` for `x ≥ x₀` does
   not imply differentiability on all of ℝ, let alone continuity of
   the derivative. The §406B residual bound applies FTC to `yex'`,
   which requires `yex'` continuous on all of ℝ.

## Why the deviation is acceptable

For any IVP that arises in practice:

* `f` smooth (typical Butcher-numerical-methods setting): joint
  Lipschitz follows from boundedness of `∂_t f` and `∂_y f` on the
  trajectory's compact tube.
* `yex` on a bounded trajectory: `M_bound = max_{t ∈ Icc} |f t (yex t)|`
  exists by compactness.
* Picard–Lindelöf (Butcher §110, our `thm:110C`) produces a C¹
  solution from Lipschitz `f`.

The strengthening rules out pathological `f`s (e.g. `f` continuous
but with arbitrarily growing `t`-modulus, or `yex` whose derivative
explodes off `[x₀, x]`) that Butcher's argument would not actually
handle either. The textbook proof tacitly uses each of these three
properties.

## Consumers

`IsConvergent` has zero downstream Lean consumers other than the
theorem we are closing (verified by grep at cycle 068). Strengthening
the predicate is therefore safe — no other proof breaks.

## Future remediation (optional)

If at some point a stronger faithfulness contract is desired, the
strengthening can be unwound by:

1. Re-deriving the cycle 064–067 helper chain under
   `LipschitzInSecond` + compact-restricted bounds + Picard–Lindelöf-
   produced C¹ solution. This is at least 3 cycles of churn for a
   strictly weaker formal result (since the new hypotheses must then
   *also* be checked against the textbook's intended class of IVPs).

2. Or proving `IsConvergent_textbook → IsConvergent_strengthened`
   under the standard Picard–Lindelöf hypotheses (Lipschitz `f`,
   bounded initial trajectory). This is the cleaner approach but
   requires `thm:110C` (`picard_lindelof`) at production strength.

Both options are out of scope for the cycle 068 closure.

## Cross-references

* `OpenMath/Chapter4/Section404.lean:305` — the strengthened predicate.
* `OpenMath/Chapter4/Section404.lean:5398` — `stable_consistent_isConvergent`,
  which consumes the strengthened predicate.
* `OpenMath/Chapter4/Section404.lean:5253` —
  `stable_consistent_isConvergent_autonomous`, the autonomous template
  that already takes all three of the strengthened hypotheses.
* `extraction/formalization_data/entities/def_402A.json` — textbook
  statement.
* `.prover-state/issues/non_autonomous_lift_plan.md` — overall
  cycle 064–068 plan; cluster 4 is the closure that motivated this
  strengthening.
