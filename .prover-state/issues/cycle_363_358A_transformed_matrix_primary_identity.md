# Issue: 358A transformed-matrix primary identity still missing after sign-helper extraction

## Blocker
The live blocker is now the primary `(358c)` bridge behind
`ButcherTableau.nodePoly_interval_zero_aux_of_algStable` in
`OpenMath/CollocationAlgStability.lean`.

After extracting a second-stage sign helper
`stabilityMatrix_quadForm_eq_neg_integral`, the remaining missing mathematics is
the **first-stage identity** that turns the algebraic-stability quadratic form
into the node-polynomial integral without assuming the lower-degree zero theorem
in advance.

Concretely, for `q : ℝ[X]` with `q.natDegree ≤ s - 1`, letting

```lean
Q(x) := ∫ t in (0 : ℝ)..x, q.eval t
```

and writing the antiderivative polynomial as

```lean
Qpoly = Polynomial.C α * nodePoly t + r
```

with `r.natDegree < s`, the proof reduces to the special exactness step

```lean
∑ i : Fin s, t.b i * q.eval (t.c i) * r.eval (t.c i)
  = ∫ x in (0 : ℝ)..1, (q * r).eval x
```

for this theorem-local remainder `r`.

That is the precise identity still missing in the live code.

## Context
- Live file: `OpenMath/CollocationAlgStability.lean`
- Live assumptions available:
  - `hcoll.2.1 : t.SatisfiesB s`
  - `hcoll.2.2.1 : t.SatisfiesC s`
  - `hcoll.2.2.2 : Function.Injective t.c`
  - `hAlg.nonneg_weights`
  - `hAlg.posdef_M`
- Existing reusable infrastructure:
  - `quadEvalPoly_exact_of_natDegree_lt_of_SatisfiesB`
  - `quadEvalPoly_nodePoly_mul_eq_zero`
  - `polyMomentN_eq_intervalIntegral_of_natDegree_lt`
  - `nodePoly_mul_natDegree_lt`

## What was tried
- Triaged Aristotle bundles `018396aa`, `52cf2a73`, and `fabcddf1` as directed.
- Rejected all bundled copies of `OpenMath/Legendre.lean`,
  `OpenMath/StiffEquations.lean`, and `lakefile.toml`.
- Salvaged only the theorem-local helper shape from `018396aa` and added the
  live scaffold:
  `ButcherTableau.stabilityMatrix_quadForm_eq_neg_integral`.
- Closed the original theorem
  `ButcherTableau.nodePoly_interval_nonpos_aux_of_algStable` by reducing it to:
  - the new sign helper
  - `hAlg.posdef_M`
  - positivity of `q.leadingCoeff / s`
- Verified `OpenMath/CollocationAlgStability.lean` and
  `lake build OpenMath.CollocationAlgStability`.

## Possible solutions
- Prove the special exactness statement above for the remainder `r` by using the
  fact that `r(c_i) = Q(c_i)` and that `Q(c_i)` comes from the `C(s)` stage
  relation, not from an arbitrary degree-`< s` polynomial.
- Re-express
  `∑ i, ∑ j, q(c_i) * t.algStabMatrix i j * q(c_j)`
  as
  `2 * quadEvalPoly t (q * r) - (∫_0^1 q)^2`,
  then identify the special reason that `quadEvalPoly t (q * r)` is exact for
  this remainder even though `q * r` can have degree up to `2*s - 2`.
- If that exactness route fails, work directly with the transformed polynomial
  basis from the textbook proof, but keep the result local to
  `CollocationAlgStability.lean` and avoid changing global APIs.
