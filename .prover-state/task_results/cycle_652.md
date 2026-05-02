# Cycle 652 Results

## Worked on
§521 — four RK-side GLM A-stability transports in
`OpenMath/RKAsGLM.lean`:

- `rkSDIRK2_toGLM_isAStable` (using `sdirk2_aStable`)
- `rkSDIRK3_toGLM_isAStable` (using `sdirk3_aStable`)
- `rkRadauIIA3_toGLM_isAStable` (skipped, see issue)
- `rkGaussLegendre3_toGLM_isAStable` (skipped, see issue)

## Approach
For each landed transport, the recipe is:

1. Build a side `t.stabilityFunction z = customStabilityFn z` bridge.
2. After `rw [ButcherTableau.stabilityFunction]`, replace the matrix
   `1 - z • Aℂ` (which has the type `Matrix.of` HSub elaboration
   issue) with an explicit `!![..]` form via `change` then `rw [hM]`.
3. Compute `det = (1 - zλ)^s` via `Matrix.det_fin_two_of` /
   `Matrix.det_fin_three; simp; ring` (lower-triangular constant
   diagonal makes this trivial).
4. `Matrix.inv_def` + `Matrix.adjugate_fin_{two,three}_of` +
   `Ring.inverse_eq_inv'` to expose `1/det • adjugate`.
5. Unfold the `b · A⁻¹` sum via `Fin.sum_univ_{two,three}` and the
   `cons_val_*` simp set, then `push_cast; field_simp; ring`.
6. The GLM transport is then a one-line
   `rw [ButcherTableau.toGLM_isAStable_iff]; intro z hz;
    rw [stabilityFunction_eq z hz]; exact ..._aStable z hz`.

The denominator non-vanishing hypothesis comes from
`sdirk{2,3}Lambda_pos` plus `hz : z.re ≤ 0`, taking real parts:
`(1 - z·λ).re = 1 - z.re·λ ≥ 1 > 0`.

Sorry-first: skeleton landed for both bridges with `sorry`, verified
compile, then individual goals closed.

## Result
SUCCESS — `rkSDIRK2_toGLM_isAStable` and `rkSDIRK3_toGLM_isAStable`
landed with no `sorry`. `lake build` completes successfully (8087
jobs); `lake env lean OpenMath/RKAsGLM.lean` compiles cleanly. No
new live `sorry` and no orphan stubs left in `OpenMath/`.

Radau IIA and GL3 explicitly skipped per strategy "do not fight the
alignment"; the obstruction is documented in
`.prover-state/issues/radau_gl3_glm_aStable_sqrt_bridge.md`.

## Dead ends
- `rw [Matrix.nonsing_inv_apply _ ...]` introduced `↑h.unit⁻¹` smul
  scalars that `field_simp; ring` could not handle. Replaced by
  `Matrix.inv_def` + `Ring.inverse_eq_inv'`, which produces a clean
  `1/det • adjugate` form.
- `Matrix.det_fin_three_of` does not exist; used
  `rw [Matrix.det_fin_three]; simp; ring`.
- HSub elaboration on `(1 : Matrix...) - z • (fun i j => ↑(rkSDIRK2.A
  i j))` failed — `z •` made the inner expression elaborate as
  `Fin s → Fin s → ℂ`, not `Matrix`. Wrapping with `Matrix.of` and
  using `change` before `rw [hM]` resolved it.
- For Radau IIA, a one-shot
  `simp only [..., Matrix.one_apply, rkRadauIIA3, ...]` followed by
  `ring` blew through the heartbeat budget; `ring` cannot fold
  `(Real.sqrt 6)^2 = 6` either way. Aborted; wrote issue file.

## Discovery
The SDIRK recipe transfers cleanly to **any lower-triangular RK
tableau with constant diagonal**: `det = (1 - zλ)^s` is immediate,
`adjugate_fin_{two,three}_of` gives a closed-form inverse, and
`field_simp; ring` finishes. This is the same pattern that closes
implicit Euler and implicit midpoint, just at higher dimension.

For full (non-triangular) tableaux with **algebraic-irrational
entries** (Radau IIA: `Real.sqrt 6`, GL3: `Real.sqrt 15`), the
determinant identity is true classically (collocation methods produce
diagonal Padé denominators) but invisible to `ring`, which treats
`Real.sqrt 6` as an opaque variable. Closing it requires either
(a) a `linear_combination` certificate encoding the cross-term
cancellation, (b) a structured `A = A₀ + sqrt·A₁` decomposition, or
(c) a generic collocation → Padé bridge that gives both Radau IIA
and GL3 (and any future collocation-based RK method) for free.

## Suggested next approach
Three independent leverage-y paths:

1. **Generic collocation → Padé bridge** in
   `OpenMath/Collocation.lean` / `OpenMath/Pade.lean`. One-time
   investment; both Radau IIA and GL3 transports become corollaries.
   This is approach (c) above and matches Iserles Theorem 4.6 /
   Hairer–Wanner Theorem IV.5.4.
2. **Hand-derived linear-combination certificate** for one of Radau
   IIA or GL3. Less invasive but error-prone; estimate 1–2 cycles
   per tableau. Approach (a).
3. **Higher-order BDF GLM transports** — BDF5 and BDF6 negative
   A-stability are blocked on classical scalar `bdf{5,6}_not_aStable`
   results, which need Dahlquist-barrier algebraic certificates,
   not additional GLM infrastructure. Lower priority unless someone
   wants to engage the classical side.
