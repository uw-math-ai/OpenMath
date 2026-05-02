# Issue: `GeneralLinearMethod.isStabilityOrder_zero` requires analytic Big-O machinery

## Blocker

The §521 sanity result

```lean
theorem isStabilityOrder_zero (m : GeneralLinearMethod s r) :
    m.IsStabilityOrder 0 := by sorry
```

asks for an explicit `C, δ > 0` with
`‖m.stabilityMatrix z - Complex.exp z • m.Vℂ‖ ≤ C * ‖z‖` for `‖z‖ < δ`.
Because `IsStabilityOrder 0` matches the standard "first-order tangency"
shape, mere continuity of `g z := stabilityMatrix z − exp z · Vℂ` at
`z = 0` is **not enough**: continuity gives `little-o(1)`, not `O(z)`.
We need either differentiability (`HasDerivAt g g' 0`) or a manual
Big-O bound on each entry.

## Context

```lean
def IsStabilityOrder (m : GeneralLinearMethod s r) (p : ℕ) : Prop :=
  ∃ C δ : ℝ, 0 < δ ∧ 0 ≤ C ∧
    ∀ z : ℂ, ‖z‖ < δ →
      ‖m.stabilityMatrix z - Complex.exp z • m.Vℂ‖ ≤ C * ‖z‖ ^ (p + 1)
```

`stabilityMatrix z = Vℂ + z • (Bℂ * (I - z • Aℂ)⁻¹ * Uℂ)` (total inverse).

The matrix norm is the local instance `Matrix.normedAddCommGroup` (the
L∞ entrywise sup norm). To convert an entrywise bound to a matrix-norm
bound we have `Matrix.norm_le_iff` (Mathlib `Analysis.Matrix.Normed`).

## What was tried

Step-by-step decomposition:

```
M(z) − exp z • V
  = z • (B (I−zA)⁻¹ U)  −  (exp z − 1) • V
```

This naturally splits the bound into two pieces:

1. **`(exp z − 1)` part.** Use `Complex.exp_sub_sum_range_isBigO_pow 1`
   (Mathlib `Analysis.SpecialFunctions.Exp`) which gives
   `(z ↦ exp z − 1) =O[𝓝 0] (z ↦ z)`. Combine with
   `Asymptotics.IsBigO.bound` to get `∃ C', ∀ᶠ z, |exp z − 1| ≤ C' * |z|`,
   then translate the `∀ᶠ z in 𝓝 0` to an explicit `δ` via
   `Metric.eventually_nhds_iff` (or a direct ε-δ unwrap). For `‖z‖ ≤ 1`
   the simpler estimate `|exp z − 1| ≤ e · ‖z‖` works (analog of
   `Real.abs_exp_sub_one_le`, which exists at type `ℝ` but a complex
   variant must be assembled from `Complex.norm_exp_le` /
   `Complex.exp_sub_sum_range_isBigO_pow 1`).

2. **`z • (B (I−zA)⁻¹ U)` part.** This is `z` times a matrix that is
   continuous at `z = 0` (its value there is `B · I · U = B · U`).
   Continuity of the inverse at `z = 0` follows from
   `continuousAt_matrix_inv` (Mathlib `Topology.Instances.Matrix`):
   given `ContinuousAt Ring.inverse (det (I − zA))` at `z = 0`
   (where `det(I − 0 • A) = 1`, and `Ring.inverse` is continuous at
   `1` in the field `ℂ`), `Inv.inv` (= `Matrix.inv`) is continuous in
   the matrix argument. Composing with `z ↦ I − z • A` (linear,
   continuous) gives continuity of `z ↦ (I − z A)⁻¹` at `0`.
   Then by continuity, on a small ball `‖z‖ < δ_1` the matrix
   `B (I − zA)⁻¹ U` has bounded norm `K`; combined with the leading
   `z` factor this gives the `‖z‖ · K` bound on this part.

Combining (1) and (2) yields `‖M(z) − exp z • V‖ ≤ (K + ‖V‖ · C') · ‖z‖`
on `‖z‖ < min δ_1 1`.

## Why this stalled this cycle

Concretely assembling the above requires a chain of at least four
non-trivial Mathlib API uses:
* `Asymptotics.IsBigO.bound` + `Metric.eventually_nhds_iff` to extract
  an explicit `(C', δ')` from a `=O[𝓝 0]` statement.
* `continuousAt_matrix_inv` plus the chain
  `ContinuousAt (Ring.inverse) 1 → ContinuousAt det → ContinuousAt
  (·⁻¹) → ContinuousAt of the composition`. The detour through
  `Ring.inverse` vs `Inv.inv` for matrices needs care because
  `Matrix.inv` (`nonsing_inv`) is `Inv.inv`, not `Ring.inverse` —
  these agree on units but the lemma is phrased on `Ring.inverse` of
  the determinant.
* Lifting an entry-bound `‖entry‖ ≤ b` to `‖matrix‖ ≤ b` uses
  `Matrix.norm_le_iff`, which expects `0 ≤ b` and a uniform per-entry
  bound. Matrix subtraction needs `Matrix.sub_apply` to expose entries.
* The final calc combining `‖A • B‖ ≤ ‖A‖ * ‖B‖` (where `•` is the
  scalar smul `ℂ → Matrix _ _ ℂ → Matrix _ _ ℂ`, requiring
  `norm_smul`).

Each step is straightforward in isolation, but stitching them together
is the work of an entire cycle.

The strategy file for cycle 616 explicitly permits this `sorry` to
remain provided the other four §521 deliverables land, and they have
(definition `IsStabilityOrder`, `IsStabilityOrder.mono`, the scalar
predicate `IsStabilityFunctionOrder`, and the bridge
`toGLM_isStabilityOrder_of_stabilityFunctionOrder`).

## Possible solutions

### Solution A — explicit ε-δ assembly (recommended next attempt)

Build the proof in two named helpers inside
`OpenMath/GeneralLinearMethod.lean`:

```lean
private theorem norm_exp_sub_one_le_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - 1‖ ≤ Real.exp 1 * ‖z‖ := by
  -- via Complex.exp_sub_sum_range_isBigO_pow 1 + IsBigO.bound, OR
  -- via direct power-series tail bound
  sorry

private theorem norm_resolvent_factor_bound (m : GeneralLinearMethod s r) :
    ∃ K δ, 0 < δ ∧ 0 ≤ K ∧
      ∀ z : ℂ, ‖z‖ < δ →
        ‖m.Bℂ * ((1 : Matrix (Fin s) (Fin s) ℂ) - z • m.Aℂ)⁻¹ * m.Uℂ‖ ≤ K := by
  -- via continuousAt_matrix_inv + composition + continuity-gives-bounded
  sorry
```

Then `isStabilityOrder_zero` is a one-screen `calc` combining the two.

### Solution B — `HasFDerivAt` route

Show `g z := stabilityMatrix z − exp z • Vℂ` has a derivative at `0`,
then apply `HasDerivAt.isBigO_sub` to get
`(z ↦ g z − g 0) =O[𝓝 0] (z ↦ z − 0)`, then `IsBigO.bound`. This
needs the matrix-inverse derivative formula and is heavier than
Solution A.

### Solution C — entrywise Cramer-rule expansion

Each entry of `(I − zA)⁻¹` is `det(M_ij(z)) / det(I − zA)`, both
polynomials in `z` (constant term 1 in the denominator). Each entry of
`M(z) − exp z V` is then a *complex-analytic* function of `z` near `0`
with value `0` at `z = 0`, so each is `O(z)` by
`AnalyticAt.isBigO_sub` (or by direct power-series). Sum the entry
bounds via `Matrix.norm_le_iff`. Conceptually the cleanest, but
unwinding `Matrix.inv` to the Cramer formula in Lean requires
`Matrix.inv_def` plus `Matrix.adjugate_apply` and is verbose.

## Mathlib search queries already tried

* `lean_loogle "Matrix.normedAddCommGroup"` — found the instance.
* `lean_loogle "Matrix.norm_le_iff"` — found the entry-bound bridge.
* `lean_leansearch "norm of 1x1 matrix equals norm of single entry"` —
  found `Matrix.norm_def`, `Matrix.nnnorm_entry_le_entrywise_sup_nnnorm`.
* `lean_leansearch "norm exp z minus 1 minus z bound"` — found
  `Complex.exp_sub_sum_range_isBigO_pow` (the right tool for the
  exp − 1 = O(z) bound).
* `lean_leansearch "matrix inverse differentiable analytic"` — found
  `Differentiable.inverse` (uses `Ring.inverse` and
  `HasSummableGeomSeries`, applicable but heavyweight).
* `lean_leansearch "Matrix inv continuous nonsingular"` — found
  `continuousAt_matrix_inv` (the cleanest hook for Solution A).

## Suggested next cycle

Open a follow-up cycle that lands `isStabilityOrder_zero` as the sole
target. Use Solution A: write the two private helpers above, each as a
~30-line proof, then close the main theorem in a 10-line `calc`. The
work is genuinely a cycle's worth — it is not a one-liner. Do **not**
attempt to inline it as a parenthetical inside a broader §521 push.
