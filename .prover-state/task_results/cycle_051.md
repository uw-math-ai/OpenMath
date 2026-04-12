# Cycle 051 Results

## Worked on
New file `OpenMath/BDF.lean`: A(α)-stability theory and extended BDF family (BDF5, BDF6).

## Approach
Followed Option A from the strategy: more stiff equations / BDF methods (Section 4.5).

### A(α)-Stability Framework
- Defined `LMM.InSector` (the wedge S_α = {z : z.re ≤ -‖z‖ · cos(α)})
- Defined `LMM.IsAAlphaStable` (stability region contains S_α)
- Proved `isAStable_iff_aAlpha_pi_div_two`: A-stability = A(π/2)-stability
- Proved `IsAAlphaStable.mono`: monotonicity (A(α) implies A(α') for α' ≤ α)
- Proved `IsAStable.toAAlphaStable`: A-stability implies A(α)-stability

### BDF Not-A-Stable Results
- `bdf3_not_aStable`: BDF3 is NOT A-stable (order 3 + zero-stable → Dahlquist barrier)
- `bdf4_not_aStable`: BDF4 is NOT A-stable (order 4 + zero-stable → Dahlquist barrier)
- `bdf5_not_aStable`: BDF5 is NOT A-stable (conditional on zero-stability)
- `bdf6_not_aStable`: BDF6 is NOT A-stable (conditional on zero-stability)

### BDF5 (5-step, new)
- Definition with correct coefficients from Iserles Table 4.1
- Consistency proof (ρ(1) = 0 and ρ'(1) = σ(1))
- Order 5 proof (V_0 = ... = V_5 = 0, V_6 ≠ 0)
- Implicit proof (β₅ = 60/137 ≠ 0)

### BDF6 (6-step, new)
- Definition with correct coefficients from Iserles Table 4.1
- Consistency proof
- Order 6 proof (V_0 = ... = V_6 = 0, V_7 ≠ 0)
- Implicit proof (β₆ = 60/147 ≠ 0)

### Backward Euler A(α)-stability
- `backwardEuler_aAlphaStable`: backward Euler (= BDF1) is A(α)-stable for all α ≤ π/2

## Result
SUCCESS — 15 sorry-free theorems in new file `OpenMath/BDF.lean`.

## Dead ends
None — all proofs compiled on the first attempt.

## Discovery
- `Fin.sum_univ_succ` is sufficient for expanding Fin sums of arbitrary size (no need for
  `Fin.sum_univ_six` or `Fin.sum_univ_seven`; the recursive `Fin.sum_univ_succ` works universally).
- `Real.strictAntiOn_cos.antitoneOn` provides the cosine monotonicity needed for A(α)-stability.
- The Dahlquist barrier (`LMM.dahlquist_second_barrier`) works cleanly as a black box for
  proving non-A-stability of higher-order BDF methods.

## Suggested next approach
- **BDF5/BDF6 zero-stability**: these are the main missing proofs. BDF5 requires showing
  roots of a degree-4 polynomial are inside the unit disk; BDF6 requires degree-5.
  Both follow the pattern of `bdf4_zeroStable` but are significantly more tedious.
- **BDF2 A-stability**: `bdf2_aStable` has not been formalized yet. The proof requires
  showing the stability polynomial's roots stay in the unit disk for Re(z) ≤ 0.
- **BDF7 not zero-stable**: define BDF7 and show it has a root outside the unit disk.
  This would complete the classical result that BDF1-6 are zero-stable but BDF7+ are not.
- **A(α)-stability angles**: proving specific A(α)-stability angles for BDF3-6 would
  require numerical estimates (e.g., BDF3 is A(86°)-stable).
