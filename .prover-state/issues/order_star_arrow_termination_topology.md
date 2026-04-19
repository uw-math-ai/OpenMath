# Issue: Order-star arrow termination needs global trajectory formalization

## Blocker
The textbook statements of Theorems 355C and 355D are about where full order arrows terminate: at poles, zeros, or infinities. The current Lean file only formalizes local tangent directions near the origin (`IsUpArrowDir`, `IsDownArrowDir`), not global arrow trajectories.

## Context
`OpenMath/OrderStars.lean` proves the local angle-selection results of Theorem 355B and the A-stability criterion of Theorem 355F. The missing gap is the intermediate global picture:
- an order arrow must continue as a connected component of the order web,
- that component cannot self-intersect or cross arrows of the opposite type,
- and its only terminal behaviors are hitting a pole/zero or escaping to infinity.

These arguments in the textbook use asymptotics of `R(z) * exp(-z)` and a global trajectory picture that is not yet encoded in the repo.

## What was tried
- Reviewed the existing local `OrderStars.lean` infrastructure around `IsUpArrowDir` and `IsDownArrowDir`.
- Checked the extracted entity data for Theorems 355C, 355D, and 355E.
- Added a finite bookkeeping layer (`OrderArrowCountData`, `SatisfiesArrowCountInequality`) so the arithmetic consequence of 355D can already be stated and used downstream without committing to a premature topological model.

## Possible solutions
- Introduce an abstract notion of an order-arrow branch as a connected component of the order web together with endpoint data.
- Prove a general "branch endpoint dichotomy" theorem for rational functions `R(z) * exp(-z)` using asymptotics at infinity and singularities of rational functions.
- If the full topology is too heavy, isolate the exact assumptions needed for downstream theorems as axioms/interfaces over arrow counts and later discharge them from a dedicated global-order-star file.
