# Cycle 654 Results

## Worked on

Butcher §521 — GLM A-stability transport for the 3-stage Gauss–Legendre
(GL3) method. Added in `OpenMath/RKAsGLM.lean`:

- `rkGaussLegendre3_stabilityFunction_eq`
- `rkGaussLegendre3_toGLM_isAStable`

Also rotated `## Current Target` in `plan.md` from §38 (paused) to
§521 GLM A-stability transports, and removed
`.prover-state/issues/radau_gl3_glm_aStable_sqrt_bridge.md` (resolved).

## Approach

Mirrored cycle 653's three-certificate split for Radau IIA verbatim,
with `s : ℂ := ((Real.sqrt 15 : ℝ) : ℂ)` and
`hs15_C : s ^ 2 = 15`:

1. **Matrix shape `hM`.** Pinned `(1 - z • A_GL3)` to an explicit dense
   3×3 `M` with `s` substituted in for `Real.sqrt 15`. Closed by
   `subst M; ext i j; fin_cases i <;> fin_cases j <;> simp [...]`.

2. **Determinant certificate `hdet`.** Proved `M.det = gl3Q z / 120`
   using `Matrix.det_fin_three` + `simp [..., gl3Q]` +
   `linear_combination (norm := ring_nf) (z ^ 2 * (12 - z) / 1800) * hs15_C`.
   The coefficient was derived by inspecting the post-`ring_nf` residual
   `(z²·s²/150 - z³·s²/1800) − (z²/10 − z³/120)`, factoring out `s² − 15`.

3. **Adjugate-weighted sum certificate `hsum`.** Proved
   `∑ i, ∑ j, (b_i : ℂ) * M.adjugate i j = (60 + z²) / 60`. The closed form
   has **no `s` dependence at all** (a clean reflection of GL3's
   diagonal-Padé symmetry — the `√15` cross-terms in `bᵀ adj(M) 1`
   completely cancel modulo `s² = 15`). Closed by
   `linear_combination (norm := ring_nf) (z ^ 2 / 900) * hs15_C`.

4. **Scalar numerator + assembly.** The classical identity
   `gl3P z − gl3Q z = 2z(60 + z²)` (already in
   `OpenMath/GaussLegendre3.lean` as `gl3_P_sub_Q`) gives the cleanup
   `gl3Q z + z · 2 · (60 + z²) = gl3P z` directly — no `hs15_C` needed
   at the assembly step. Then `Matrix.inv_def`, `Ring.inverse_eq_inv'`,
   `inv_div`, `inv_mul_cancel₀ hD`, and a small `calc` block land at
   `gl3StabilityFn z`. Used `gl3_Q_ne_zero` for the non-vanishing fact
   on `z.re ≤ 0`.

## Result

SUCCESS. `lake env lean OpenMath/RKAsGLM.lean` clean (only pre-existing
unused-simp-arg lint warnings on `rkSDIRK2` / `rkSDIRK3` proofs), and
`lake build` reports 8087 jobs successful — identical to cycle 653.

## Three certificate coefficients (cycle artefact)

For future collocation bridges, the cycle 654 GL3 coefficients are:

- Determinant: `(z² (12 − z) / 1800) · (s² − 15)`, with target
  `gl3Q z / 120 = (120 − 60z + 12z² − z³) / 120`.
- Adjugate sum: `(z² / 900) · (s² − 15)`, with target `(60 + z²) / 60`.
  (This is *much* cleaner than the Radau IIA counterpart, which carried
  s²-dependent terms in its closed form.)
- Numerator/assembly: closed via `gl3_P_sub_Q` rather than
  `linear_combination ⋯ * hs15_C` — no s² cleanup needed because the
  adjugate-sum closed form is s²-free.

The s²-free adjugate sum is the structurally interesting outcome:
GL3's symmetry (Gauss–Legendre nodes are symmetric about 1/2 with
`b₁ = b₃ = 5/18`, and `A` is anti-symmetric in `s` under the swap
of rows 0/2 and columns 0/2) means the `bᵀ adj(M) 1` sum is invariant
under `s → −s`, hence its `s¹`-coefficient vanishes identically and
its `s²`-coefficient is forced to be the polynomial `z²/900` modulo
`s²=15`.

## Dead ends

- Initially tried the `(60 + z²)/60` closed form with bare `ring_nf`;
  the residual was `1 + z²·s²/900 = 1 + z²/60`, requiring `s² = 15`.
  Switched to `linear_combination`. (Identical pattern to Radau IIA
  cycle 653.)
- Stray `rw [show ((Real.sqrt 15 : ℝ) : ℂ) = s from rfl]` carried over
  from the Radau template was redundant (`simp` already substitutes
  `↑√15 → s` because `s` is a local `let`-binding); removed.

## Discovery

For methods whose coefficient matrix is anti-symmetric in `√d` under
a row/column swap (Gauss–Legendre, possibly also Lobatto IIIA, Radau IA
in their canonical orderings), the `bᵀ adj(M) 1` closed form is
`s`-free as a polynomial modulo `s² = d`. This collapses the
"scalar numerator" certificate to a single `gl3_P_sub_Q`-style
`linear_combination` over `gl3P − gl3Q` — no `hs_C` needed at
assembly. Future collocation bridges should check this symmetry first
before computing the scalar numerator coefficient by hand.

## Suggested next approach

1. **Lobatto IIIA / IIIB / IIIC.** Same recipe, leveraging the
   `√?` symmetry where applicable. Stability functions for these are
   classical Padé approximants too.
2. **DIRK / ESDIRK families** beyond SDIRK2/3.
3. **`LMM.toGLM_isAStable_iff` general charpoly factorisation.** See
   `.prover-state/issues/lmm_toGLM_general_charpoly_rank_one.md`.
4. Long-term: §38 Butcher group remains paused on the `cut_assoc`
   obstruction; do not pivot back without a structured plan.
