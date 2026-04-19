# Issue: Legendre orthogonality bridge still blocks `gaussLegendre_B_double`

## Blocker
`OpenMath/Legendre.lean` still has the two remaining sorrys in
`ButcherTableau.gaussLegendre_B_double` and
`ButcherTableau.gaussLegendreNodes_of_B_double`.

The immediate blocker for closing `gaussLegendre_B_double` is not the defect
subtraction step itself. The missing piece is a usable, sorry-free bridge from
the recursive `shiftedLegendreP` to coefficients with a proved orthogonality
identity.

## Context
The current target inside `gaussLegendre_B_double` is the high-degree branch

```lean
⊢ ∑ i, t.b i * t.c i ^ (s + j) = 1 / ↑(s + j + 1)
```

for `j < s`, assuming:

```lean
hGL : ∀ i : Fin s, shiftedLegendreP s (t.c i) = 0
hB  : ∀ k, 1 ≤ k → k ≤ s → ∑ i, t.b i * t.c i ^ (k - 1) = 1 / ↑k
```

The clean route is still:
1. represent `shiftedLegendreP s` by coefficients `a l`,
2. prove `∑ l, a l / (l + j + 1) = 0` for `j < s`,
3. subtract that identity from the GL node relation to isolate the unknown
   moment `S (s + j)`.

## What was tried
1. Checked all seven planner-listed Aristotle jobs first.
   - `d206f904-7ca0-487b-a04d-810746020839`: `COMPLETE_WITH_ERRORS`
   - `9d969800-dcdf-43bf-9b3a-0b2d6cf1f8f6`: `IN_PROGRESS` at 38%
   - `25f0bc02-fd9c-4e56-a5fe-dcb75e9a92c0`: `COMPLETE`
   - `88562ee9-0604-4af8-af76-4cd109783926`: `IN_PROGRESS` at 37%
   - `c9418788-b71f-4072-bab7-238eaf5b1ea8`: `IN_PROGRESS` at 32%
   - `de165c89-6ceb-4a51-a674-ee4da6c4264b`: `COMPLETE_WITH_ERRORS`
   - `1d9822aa-9d1d-4d23-abf6-501995a5f6a8`: `COMPLETE`
2. Extracted the completed outputs.
   - The bridge-only job proves a sign-twisted equivalence with
     `Polynomial.shiftedLegendre`, but only in an external Aristotle project
     and with `set_option maxHeartbeats 800000`.
   - The full-file job introduces a helper file and still contains unfinished
     parts (`exact?` / incomplete helper development), so it is not directly
     transplantable.
3. Explored two local proof paths.
   - Algebraic integration-by-parts on polynomial coefficients.
   - Explicit coefficient orthogonality via a generating-function identity.

## Possible solutions
1. Finish the bridge locally, but keep it inline.
   - The usable statement is:
     `shiftedLegendreP n x = (-1 : ℝ)^n * eval x (map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre n))`.
   - The extracted Aristotle proof is the best current template, but it needs
     a substantial simplification pass before it can live inside
     `gaussLegendre_B_double` without violating the heartbeat constraint.
2. Avoid the full bridge and prove orthogonality from explicit coefficients.
   - After the sign change, the needed coefficients are
     `a_l = (-1)^(s + l) * (s.choose l) * ((s + l).choose s)`.
   - The key identity reduces to
     `∑ i=0..s (-1)^i * (s.choose i) * ((s + j - i).choose (s - 1)) = 0`
     for `j < s`.
   - This identity has a clean generating-function proof:
     it is the coefficient of `X^(s-1)` in
     `((1 + X) - 1)^s * (1 + X)^j = X^s * (1 + X)^j`,
     hence zero.
3. If the explicit-coefficient route is resumed, attack the coefficient lemma
   directly instead of the full quadrature theorem.
   - Prove the generating-function identity as a standalone combinatorial fact
     in a scratch file first.
   - Then convert it into the orthogonality statement needed by the defect
     subtraction argument.
