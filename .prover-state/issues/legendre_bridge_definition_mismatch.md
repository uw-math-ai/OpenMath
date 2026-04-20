# Issue: Aristotle bridge proof targets obsolete Legendre definition

## Blocker
The completed Aristotle bridge result from project `819194af-66fe-4d07-90ce-35de882ff419`
does not apply to the current `OpenMath.Legendre.shiftedLegendreP` source.

## Context
The returned proof assumes the sum-form definition of `shiftedLegendreP`:

```lean
shiftedLegendreP n x =
  ∑ k ∈ Finset.range (n + 1), (-1)^(n+k) * C(n,k) * C(n+k,n) * x^k
```

but the current file [OpenMath/Legendre.lean](/mmfs1/gscratch/amath/mathai/OpenMath/OpenMath/Legendre.lean:50)
defines `shiftedLegendreP` recursively by the three-term recurrence.

## What was tried
- Inserted the harvested theorem directly into `OpenMath/Legendre.lean`
- Moved the harvested proof into a separate helper module importing `OpenMath.Legendre`
- Re-ran local compilation for both approaches

## Possible solutions
- Prove the bridge theorem by induction from the recursive definition and Mathlib's polynomial formula
- Introduce an auxiliary sum-form polynomial/function and prove equivalence to the recursive definition first
- Ask Aristotle for a new bridge proof against the current recursive source, not the old sum-form version
