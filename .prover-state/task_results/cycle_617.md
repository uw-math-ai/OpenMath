# Cycle 617 Results

## Worked on
Butcher §501/§511 covariance of general linear methods under the input
transformation `(A, U, B, V) ↦ (A, U T⁻¹, T B, T V T⁻¹)` in
`OpenMath/GeneralLinearMethod.lean`.

## Approach
Added `GeneralLinearMethod.transform` with projection simp lemmas, then
proved the §511 algebraic transport facts by rewriting the existing
sum-based stage/step/preconsistency/consistency equations through
`Matrix.mulVec`.

The reusable local facts were:
- `(M * Tinv).mulVec (T.mulVec v) = M.mulVec v` from `Tinv * T = 1`.
- `(T * M * Tinv).mulVec (T.mulVec v) = T.mulVec (M.mulVec v)`.
- `(T * M).mulVec v = T.mulVec (M.mulVec v)`.

I submitted the sorry-first file to Aristotle as project
`d7ed48a6-95dd-4917-86fa-e5b008514b1e`; the single status check showed
`IN_PROGRESS`, so the elementary matrix rewrites were closed manually.

## Result
SUCCESS. Closed:
- `GeneralLinearMethod.transform`
- `transform_A`, `transform_U`, `transform_B`, `transform_V`
- `transform_stageMap_eq`
- `transform_step_eq`
- `transform_isPreconsistent`
- `transform_isConsistent`

`plan.md` now marks §501 and §511 closed and removes the completed §511
backlog item.

Verification:
- `lake env lean OpenMath/GeneralLinearMethod.lean`
- `rg -n "\\bsorry\\b|admit" OpenMath/GeneralLinearMethod.lean`
- LSP `lean_verify` on the four new theorem names reported no source
warnings and only the usual imported axioms.

## Dead ends
Using broad `simp` on the step/consistency vector equalities normalized
nested `mulVec` terms into matrix products too early. The fix was to use
`simp only` for the definitional row-sum conversions and reserve
`Matrix.mulVec_mulVec` for the explicit helper lemmas.

## Discovery
For square matrices, `mul_eq_one_comm` cleanly converts the predicate
transport hypotheses from the exposed right-inverse law `T * Tinv = 1`
to the internal law `Tinv * T = 1` needed by the row-sum proofs.

## Suggested next approach
Pick up backlog item #2: Butcher §515 GLM Dahlquist equivalence. The
§510 predicates, §511 covariance, and §520 stability matrix surface are
now all in place for the convergence chain.
