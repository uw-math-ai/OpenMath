# Cycle 389 Results

## Worked on
Fallback consolidation in `OpenMath/AdamsMethods.lean`, after the §1.3/§2.2
textbook lookup did not support the planned quantitative-rate theorem.

## Approach
Checked the accessible Iserles source. In the second edition, "Order and
convergence of multistep methods" is §2.2, and the named theorem found there is
Theorem 2.2, the Dahlquist equivalence theorem. Its starting-value hypothesis is
that the errors in `y₁, y₂, ..., y_{s-1}` tend to zero as `h → 0+`; the theorem
states convergence iff the method has order `p ≥ 1` and `ρ` obeys the root
condition. I did not find a separate named quantitative `O(h^p)` starting-error
theorem in the available source, so I did not invent one.

For the fallback, audited the repeated AB/AM zero-stability proofs. They all use
the same characteristic polynomial shape `ρ(ξ) = ξ^k(ξ - 1)` with a nonzero
derivative at `1`, differing only in concrete coefficient simplification. I
introduced `adams_zeroStable_of_rhoC_pow_mul` and rewired AB2--AB6 and
AM2--AM6 zero-stability theorems through it.

## Result
SUCCESS. `OpenMath/AdamsMethods.lean` now has a reusable zero-stability helper
and the file shrank from 567 to 462 lines, a net reduction of 105 lines while
preserving all public theorem names.

Aristotle:
- Submitted project `3d933e59-5698-4072-9274-1f604cdf13be` for the single
  isolated helper sorry.
- Waited 30 minutes and performed one status refresh.
- Result status: `COMPLETE`.
- Rejected the returned file because the bundle rebuilt a local
  `OpenMath/MultistepMethods.lean` stub dependency rather than proving against
  the live repository interface. The helper was closed manually against the live
  code.

## Dead ends
The planned §1.3 quantitative multistep convergence-rate theorem could not be
confirmed from the accessible textbook source. The source lookup found only the
qualitative Dahlquist equivalence statement in §2.2 / Theorem 2.2.

## Discovery
The Adams zero-stability proofs are all instances of the same root-condition
argument:

`ρ(ξ) = ξ^k(ξ - 1)`, `0 < k`, and `ρ'(1) ≠ 0` imply every root is either `0`
or `1`; the only unit-circle root is `1`, where the derivative is nonzero.

## Suggested next approach
For the next theorem cycle, do not target a quantitative §1.3/§2.2 multistep
rate theorem unless a primary source with the precise statement is available.
Theorem 359D still requires a primary-source lookup. Otherwise continue with a
real Chapter 4/BDF downstream theorem or another consolidation only if it removes
genuine duplication.
