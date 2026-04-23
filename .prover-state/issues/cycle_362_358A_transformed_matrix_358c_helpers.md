# Issue: 358A transformed-matrix `(358c)` helpers in `CollocationAlgStability`

## Blocker
The live blocker for Theorem 358A is now concentrated into the theorem-local
helper

```lean
lemma ButcherTableau.nodePoly_interval_zero_aux_of_algStable
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable) :
    ∀ q : ℝ[X], q.natDegree < s - 1 →
      ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x = 0
```

and the still-missing companion sign statement for degree-`s - 1` test
polynomials.

The rejected Aristotle bundle closed the analogous theorem only by using a fake
strengthening of `IsAlgStable` with an extra `satisfiesB_enhanced` field. That
route is not available in the live repository.

## Context
- Live file: `OpenMath/CollocationAlgStability.lean`
- Live `IsAlgStable` only gives:
  - nonnegative weights
  - `posdef_M : ∀ v, 0 ≤ ∑ i, ∑ j, v i * t.algStabMatrix i j * v j`
- Existing reusable infrastructure that should not be duplicated:
  - `polyMomentN_eq_of_natDegree_lt`
  - `quadEvalPoly_exact_of_natDegree_lt_of_SatisfiesB`
  - `nodePoly_mul_natDegree_lt`
  - `quadEvalPoly_nodePoly_mul_eq_zero`
  - `polyMomentN_eq_intervalIntegral_of_natDegree_lt`
  - `poly_eq_zero_of_intervalIntegral_sq_zero`

## What was tried
- Triaged Aristotle project `314a6a62-23a9-4572-a6b4-be80da8c324c`.
- Rejected the bundle copies of `OpenMath/Legendre.lean` and
  `OpenMath/StiffEquations.lean` because they are stub replacements of live
  files.
- Rejected the bundle proof of
  `nodePoly_polyMoment_orthogonal_of_algStable` because it depends on a fake
  `hAlg.satisfiesB_enhanced`.
- Added the live theorem-local helper scaffold
  `nodePoly_interval_zero_aux_of_algStable`.
- Closed the former interval/moment pair on top of that helper:
  - `nodePoly_interval_orthogonal_of_algStable`
  - `nodePoly_polyMoment_orthogonal_of_algStable`
- Verified the live file still compiles with the reduced sorry frontier.

## Possible solutions
- Formalize the collocation interpolation identities from `B(s)`, `C(s)`, and
  injective nodes, then express the quadratic form from `hAlg.posdef_M` as the
  quadrature error of a degree-`2s - 1` polynomial whose quotient by
  `nodePoly t` gives the `(358c)` test polynomial.
- Alternatively, work directly in the transformed polynomial basis used in the
  textbook proof, but keep the result local to `CollocationAlgStability.lean`
  instead of introducing a new general API.
- After the zero helper is proved, add the companion sign helper for
  degree-`s - 1` test polynomials and use it to derive
  `boundary_theta_nonneg_of_algStable`.
