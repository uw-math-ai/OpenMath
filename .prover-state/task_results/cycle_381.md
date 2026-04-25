# Cycle 381 Results

## Worked on
Added the Adams-Moulton 3-step (AM3) linear multistep method and its basic
properties, following the cycle 381 strategy.

## Approach
Mirrored the cycle 380 AB3 implementation:

1. Added `noncomputable def adamsMoulton3 : LMM 3` in
   `OpenMath/MultistepMethods.lean` with
   α = ![0, 0, -1, 1] and β = ![1/24, -5/24, 19/24, 9/24].
2. Added `adamsMoulton3_consistent` using `Fin.sum_univ_four` and `norm_num`.
3. Added `adamsMoulton3_implicit` using the existing `LMM.IsImplicit`
   predicate.
4. Added `adamsMoulton3_order_four` by checking `q = 0..4` with
   `interval_cases q` and the nonzero residual at `q = 5`.
5. Added `adamsMoulton3_zeroStable` by copying the AB3 zero-stability proof,
   since AM3 has the same first characteristic polynomial
   `ρ(ξ) = ξ^3 - ξ^2 = ξ^2(ξ - 1)`.
6. Added `adamsMoulton3_convergent` in
   `OpenMath/DahlquistEquivalence.lean` via `dahlquist_equivalence`.
7. Updated `plan.md` §1.2 with the AM3 completion bullet.

The sorry-first scaffold was checked before closing proofs:
- `lake env lean OpenMath/MultistepMethods.lean` compiled with the expected
  AM3 scaffold warnings.
- After rebuilding `OpenMath.MultistepMethods` so the import was current,
  `lake env lean OpenMath/DahlquistEquivalence.lean` compiled with the
  expected convergence scaffold warning.

## Result
SUCCESS. AM3 is fully formalized with no live `sorry`s in the new
declarations.

Final verification:
- `lake env lean OpenMath/MultistepMethods.lean`
- `lake env lean OpenMath/DahlquistEquivalence.lean`
- `lake build OpenMath.MultistepMethods`
- `lake build OpenMath.DahlquistEquivalence`

All completed successfully. Existing unrelated linter warnings in
`MultistepMethods.lean` and `SpectralBound.lean` remain unchanged.

## Aristotle batch
Skipped by design. The cycle strategy explicitly said to skip Aristotle for
AM3 unless a proof failed after one honest manual attempt, because this was a
mechanical AB3 mirror. All AM3 proofs closed directly on the first manual
pass, so no Aristotle jobs were submitted.

Aristotle job results: none submitted.

## Dead ends
None. The only transient issue was that `DahlquistEquivalence.lean` initially
saw a stale `OpenMath.MultistepMethods` import during the sorry-first check;
rebuilding `OpenMath.MultistepMethods` made the new AM3 declaration visible.

## Discovery
The AM3 extension confirms the AB3 zero-stability proof can be reused
unchanged for Adams-Moulton methods with the same
`α = (0, 0, -1, 1)`. The order-4 proof is also a direct arithmetic extension
of `adamsMoulton2_order_three`.

## Suggested next approach
Proceed to AB4 or AM4 as planned. AB4 should be another one-cycle addition
using `Fin.sum_univ_five`, order 4, explicitness from β at the last index
being zero, and the zero-stability template for
`ρ(ξ) = ξ^4 - ξ^3 = ξ^3(ξ - 1)`.
