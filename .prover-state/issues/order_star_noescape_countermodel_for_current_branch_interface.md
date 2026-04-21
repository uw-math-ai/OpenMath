# Issue: Current no-escape helper is false for the abstract branch interface

## Blocker
The isolated helper theorem
`orderArrowBranch_not_escape_of_rationalApprox` is not derivable from the live
hypotheses, and the problem is stronger than a missing proof: under the current
definitions it has direct countermodels.

## Context
The live helper shape is:

```lean
theorem orderArrowBranch_not_escape_of_rationalApprox
    (R : ℂ → ℂ) (data : OrderArrowTerminationData)
    (h_approx : IsRationalApproxToExp data)
    (branch : GlobalOrderArrowBranch R)
    (hescape : EscapesEveryClosedBall branch) : False
```

Current abstractions are too weak for this conclusion:

- `IsRationalApproxToExp data` does not mention `R` at all.
- `GlobalDownArrowBranch` / `GlobalUpArrowBranch` record a tangent direction and a
  global branch support, but they do not assert that the support follows that local
  arrow germ near the origin.
- `GlobalOrderArrowBranch` only requires:
  - connected support,
  - support contained in `orderWeb R`,
  - `0 ∈ closure support`.

This allows artificial escaping branches unrelated to the intended rational
approximation geometry.

Concrete countermodel sketch:

- Down-arrow case: `R(z) = (1 / 2) * exp z`.
  Then `R(z) * exp(-z) = 1 / 2`, so `orderWeb R = univ`, angle `0` is a down-arrow
  direction, and the branch with `support = univ` satisfies
  `EscapesEveryClosedBall`.
- Up-arrow case: `R(z) = 2 * exp z`.
  Then `R(z) * exp(-z) = 2`, so `orderWeb R = univ`, any angle is an up-arrow
  direction, and again `support = univ` escapes every closed ball.
- Because `IsRationalApproxToExp data` constrains only `data`, one can choose
  `data.downArrowsAtInfinity = 1` or `data.upArrowsAtInfinity = 1` with the other
  bookkeeping fields trivial, satisfy `h_approx`, and realize the infinity count by
  reusing the escaping branch for the unique `Fin 1` witness.

So the current helper theorem would force `False` in a model where all hypotheses
are satisfiable.

## What was tried
- Isolated the two count-level wrapper theorems behind one shared helper theorem.
- Checked the live proof state: after extracting the witness branch from
  `RealizesInfinityCounts`, the only remaining goal is `False`.
- Inspected the branch interfaces and found no hypothesis linking the branch support
  to the local `IsDownArrowDir` / `IsUpArrowDir` germ.
- Verified that the branch dichotomy theorems are currently trivial because
  `HasFiniteEndpoint` accepts any point in `closure branch.support`, so the origin
  itself closes both goals.

## Possible solutions
- Add one honest theorem or hypothesis connecting a global branch witness to the
  actual rational-approximation order-star asymptotics, for example:
  - a theorem that a realized infinity branch of a genuine rational approximation
    cannot stay in `orderWeb R` while escaping every closed ball, or
  - a theorem that a global down/up branch must continue the corresponding local
    down/up arrow germ near the origin, together with an asymptotic contradiction.
- Keep the repair as a theorem-level bridge. Do not hide it inside new surrogate
  fields unless the planner explicitly decides the interface must change.
