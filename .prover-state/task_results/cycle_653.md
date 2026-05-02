# Cycle 653 Results

## Worked on
§521 GLM A-stability transport for the 3-stage Radau IIA RK method in
`OpenMath/RKAsGLM.lean`:

- `rkRadauIIA3_stabilityFunction_eq`
- `rkRadauIIA3_toGLM_isAStable`

## Approach
Followed the cycle-652 SDIRK bridge, but split the dense Radau IIA algebra
into local certificates instead of one fully expanded inverse proof.

The proof introduces `s = ((Real.sqrt 6 : ℝ) : ℂ)` and uses
`hs6_C : s ^ 2 = 6`. The explicit matrix
`M = 1 - z • Aℂ` is proved by `ext + fin_cases`.

The determinant certificate landed as:

```lean
linear_combination (norm := ring_nf)
  (-z ^ 2 * (93 * z - 413) / 45000) * hs6_C
```

The adjugate-weighted sum is proved separately:

```lean
∑ i, ∑ j, (rkRadauIIA3.b i : ℂ) * M.adjugate i j =
  (93 * s ^ 2 * z ^ 2 + 250 * s ^ 2 * z + 192 * z ^ 2 - 6000 * z + 45000) / 45000
```

The scalar numerator certificate is:

```lean
linear_combination (norm := ring_nf)
  (z ^ 2 * (93 * z + 250) / 45000) * hs6_C
```

Aristotle was attempted as required, but both `submit_directory` and
`submit_file` timed out after 120 seconds without returning a project id, so
there was no result to wait on or incorporate.

## Result
SUCCESS.

`rkRadauIIA3_stabilityFunction_eq` and `rkRadauIIA3_toGLM_isAStable` are
sorry-free in `OpenMath/RKAsGLM.lean`.

Verification:

- `lake env lean OpenMath/RKAsGLM.lean` succeeds.
- `lake build` succeeds: 8087 jobs.

## Dead ends
The first direct inverse expansion left scaled denominator inverses like
`(6000 - 3600*z + 900*z^2 - 100*z^3)⁻¹` in the post-`field_simp` goal.
Trying to clear those with an auxiliary nonzero lemma made the goal larger.
Splitting out the adjugate-weighted sum avoided that problem entirely.

## Discovery
For dense algebraic RK tableaux, a useful pattern is:

1. Prove `det M = D`.
2. Prove `bᵀ adj(M) 1 = S` as a separate polynomial identity.
3. Use `M⁻¹ = D⁻¹ • adj(M)` and a short scalar calculation.

This avoids the large `field_simp` goal that appears when all adjugate entries,
weights, denominator inverses, and scalar stability functions are expanded at
once.

## Suggested next approach
GL3 should be a realistic one-cycle follow-up with the same structure:
derive the `√15` determinant and adjugate-sum certificates, then reuse the
same scalar proof shape. The direct Radau IIA bridge confirms that the
certificate split is more robust than a one-shot inverse expansion.
