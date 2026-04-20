# Cycle 209 Results

## Worked on
- `OpenMath/Legendre.lean`
- target lemma `poly_eq_zero_of_intervalIntegral_sq_zero`
- dependent theorem `ButcherTableau.gaussLegendreNodes_of_B_double`

## Approach
- Confirmed there were no completed Aristotle results ready for incorporation at cycle start.
- Read the local reduction around `polyMomentN_eq_intervalIntegral_of_natDegree_lt`,
  `poly_eq_zero_of_intervalIntegral_sq_zero`, and `gaussLegendreNodes_of_B_double`.
- Replaced the existing measure-theoretic `ae` proof of
  `poly_eq_zero_of_intervalIntegral_sq_zero` with a smaller helper-based argument:
  `eval_eq_zero_on_Icc_imp_eq_zero` and `exists_eval_ne_zero_on_Icc`.
- Used finite-roots-on-`ℝ` plus the infinitude of `Set.Icc (0:ℝ) 1` to show a nonzero
  polynomial cannot vanish on all of `[0,1]`.
- Used `intervalIntegral.integral_pos` directly on `0..1` with continuity of
  `fun x => (p.eval x)^2`, nonnegativity of squares, and a positive witness in `[0,1]`
  to contradict the hypothesis that the integral is zero.
- Kept the surrounding converse proof structure unchanged; after the helper rewrite,
  `gaussLegendreNodes_of_B_double` remained closed.

## Result
- `poly_eq_zero_of_intervalIntegral_sq_zero`: SUCCESS
- `ButcherTableau.gaussLegendreNodes_of_B_double`: already closed by the in-tree reduction and
  remains proved after the helper rewrite
- `OpenMath/Legendre.lean`: compiles successfully

## Dead ends
- Did not extend the earlier `ae_zero` / restricted-measure argument further; the helper-based
  positivity proof was shorter and more stable in the current API.

## Discovery
- The local uniqueness step can be proved with no measure-zero root-set bridge:
  `Polynomial.finite_setOf_isRoot` plus `Set.Icc_infinite` is enough to force a witness
  `x ∈ [0,1]` with `p.eval x ≠ 0`.
- Once such a witness exists, `intervalIntegral.integral_pos` on the full interval `0..1`
  is sufficient; no explicit small-interval monotonicity lemma is needed.

## Suggested next approach
- If further cleanup is desired later, the new local helpers are the right place to generalize;
  the Gaussian-quadrature converse no longer needs additional positivity infrastructure.

## Aristotle
- No completed Aristotle results were ready for incorporation at cycle start.
- Wrote sorry-first scratch decomposition in
  `.prover-state/aristotle/cycle_209_legendre_pos.lean`.
- Verified the scratch file with:
  `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean .prover-state/aristotle/cycle_209_legendre_pos.lean`
- Submitted Aristotle project:
  `19334370-65c3-45bd-991f-0bfb1139bb5d`
- Submission prompt: fill the sorries for the positivity bridge around
  `poly_eq_zero_of_intervalIntegral_sq_zero`.
- Final Aristotle status check in this cycle:
  `IN_PROGRESS` (6% complete at refresh time), so there were no Aristotle proofs
  available to incorporate into `OpenMath/Legendre.lean`.

## Verification
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/Legendre.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean .prover-state/aristotle/cycle_209_legendre_pos.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build`
