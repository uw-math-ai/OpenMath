# Cycle 386 Results

## Worked on
Adams–Moulton 5-step (AM5) method in `OpenMath/AdamsMethods.lean`, with
convergence corollary in `OpenMath/DahlquistEquivalence.lean`. Mechanical
mirror of the AB5 (cycle 384) and AM4 (cycle 383) patterns.

## Approach
Followed the strategy verbatim:
- `noncomputable def adamsMoulton5 : LMM 5` with
  α = ![0, 0, 0, 0, -1, 1] and
  β = ![27/1440, -173/1440, 482/1440, -798/1440, 1427/1440, 475/1440].
- `adamsMoulton5_consistent` — mirror of `adamsBashforth5_consistent` using
  `Fin.sum_univ_succ` plus `norm_num`.
- `adamsMoulton5_implicit : adamsMoulton5.β 5 ≠ 0` — `change` + `norm_num`,
  mirror of `adamsMoulton4_implicit`.
- `adamsMoulton5_order_six` — `interval_cases q` over q < 6 with
  `simp [LMM.orderCondVal, adamsMoulton5, Fin.sum_univ_succ]; norm_num`.
- `adamsMoulton5_zeroStable` — verbatim transplant of the AB5 ρ argument
  (ρ(ξ) = ξ⁴(ξ − 1)), substituting `adamsMoulton5` for `adamsBashforth5`.
- `adamsMoulton5_convergent` in `DahlquistEquivalence.lean` — wrapper around
  `dahlquist_equivalence` using the consistency and zero-stability witnesses.

## Result
SUCCESS. All proofs compiled on the first attempt — no β-flip needed, no
order-condition decomposition needed, no Aristotle help.

Verification:
- `lake env lean OpenMath/AdamsMethods.lean` — clean.
- `lake env lean OpenMath/DahlquistEquivalence.lean` — clean (after rebuilding
  the `OpenMath.AdamsMethods` .olean).
- `lake build` — green (8067 jobs).

## Aristotle bundles triaged
Per strategy, both ready Aristotle bundles
(`64fae740-…` and `3f458c9b-…`) were rejected as stale BDF7 artifacts:
- Both targeted `bdf7_cayley_image_root`, which has been a sorry-free
  certificate on `main` since cycle 379.
- Both rewrote `import OpenMath.Basic` to `import Mathlib`, marking them as
  non-live transplants.
No new Aristotle batch was submitted this cycle (mechanical work).

## Dead ends
None. The whole task closed cleanly on first try.

## Discovery
The β orientation for Adams–Moulton in the live convention (β 0 oldest,
β (Fin.last s) implicit/newest) is consistent across AM2/AM3/AM4/AM5; the
textbook AM5 coefficients drop in directly without sign flips. Future Adams
extensions can use the same orientation without re-deriving.

## Suggested next approach
- AB6 is the next mechanical Adams target. Iserles' explicit 6-step method
  has α = ![0,0,0,0,0,-1,1] and a quintuple root at 0 in ρ(ξ) = ξ⁶ − ξ⁵; the
  zero-stability proof transplants from AB5/AM5 with the exponent bumped to
  5. The β coefficients have multiple printings in the literature
  (denominators 60480 vs. 1440 vs. 720), so cross-reference Iserles §1.2
  before committing — do NOT pull from a chained source.
- After AB6, the next mechanical step is AM6 (implicit order-7 6-step).
- After the Adams family is exhausted, switch to Theorem 359D or pick up
  `thm_358A_if` (the boundary → PSD direction) using the Lagrange-basis
  route already sketched in
  `.prover-state/issues/thm_358A_if_boundary_to_algstable.md`.
