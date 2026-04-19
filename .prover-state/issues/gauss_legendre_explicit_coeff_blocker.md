# Issue: Explicit-Coefficient Blocker For `gaussLegendre_B_double`

## Blocker
The most plausible sorry-free route for `ButcherTableau.gaussLegendre_B_double` is:
1. bridge `shiftedLegendreP` to `Polynomial.shiftedLegendre`
2. read off explicit coefficients from `Polynomial.coeff_shiftedLegendre`
3. prove the orthogonality identity
   `∑ a_l / (l + j + 1) = 0` for `j < s`
4. run the defect-subtraction induction already described in the planner

The defect-subtraction step is not the blocker. The blocker is the orthogonality input in a form Lean will accept inside the current project.

## Context
During cycle 157, the following bridge / orthogonality attempt was partially implemented and then reverted because it broke compilation:
- bridge target:
  `shiftedLegendreP n x = (-1 : ℝ)^n * (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre n)).eval x`
- orthogonality target:
  `∑ k ∈ Finset.range (n + 1),
      ((-1 : ℝ) ^ (n + k) * (n.choose k : ℝ) * ((n + k).choose k : ℝ)) /
      ((k : ℝ) + (j : ℝ) + 1) = 0`

Concrete subgoals that stalled:
- proving
  `Q.eval (k : ℝ) = ((n + k).choose k : ℝ) / (k + j + 1)`
  for
  `Q := (∏ i ∈ (Finset.range n).erase j, (Polynomial.X + Polynomial.C ((i : ℝ) + 1))) * Polynomial.C (1 / (n.factorial : ℝ))`
- proving
  `Q.natDegree = n - 1`
  for the same erased-product polynomial
- keeping the bridge proof lightweight enough to live inline in `Legendre.lean`

## What was tried
- Harvested Aristotle results `25f0bc02-...`, `88562ee9-...`, `1d9822aa-...`, and `de165c89-...`.
- Attempted to adapt the harvested explicit-coefficient proof into the current file without changing theorem statements.
- Attempted to adapt the harvested bridge theorem showing the sign-correct relation to `Polynomial.shiftedLegendre`.
- Rejected the alternative Aristotle proof that changed `HasGaussLegendreNodes` to package coefficients and orthogonality, because it is incompatible with the existing project statement.
- Reverted the local proof experiment after it left `OpenMath/Legendre.lean` non-compiling.

## Possible solutions
- Wait for Aristotle prompts submitted at the end of cycle 157:
  - `ab7bcb15-9bf3-4e68-aa44-9f23af3fd389` for the `Q.eval` / `Q.natDegree` subgoals
  - `4b067256-1428-4cc9-aed6-c5a7ee027ce5` for the bridge theorem
- If the bridge theorem is obtained cleanly, keep the polynomial representation inline and only externalize fully proved combinatorial lemmas if necessary.
- Alternative fallback: prove orthogonality directly from `Polynomial.factorial_mul_shiftedLegendre_eq` by an algebraic “integral of coefficients” functional, but this still needs a clean repeated-integration-by-parts formalization.
