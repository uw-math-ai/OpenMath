# Cycle 076 Results

## Worked on
- Fixed Lean 4.28/Mathlib regression errors across multiple files
- Fixed compilation errors in new files (Adjoint.lean, EmbeddedRK.lean)
- Fixed mathematical errors in Adjoint.lean (Lobatto IIIA/IIIB 2-stage NOT self-adjoint)
- Added BDF5 and BDF6 definitions with consistency and order proofs
- Submitted SDIRK3 sorrys to Aristotle (project ed586e72)

## Approach
1. Restored NVMe cache (Mathlib oleans evicted)
2. Fixed StiffAccuracy.lean: GL3 nlinarith hint (sq_sqrt), IIIB2 index (h 0 → h 1)
3. Fixed Adjoint.lean: consistent_iff proof (Finset.sum_congr), field notation (dot notation on proof terms), corrected false theorems (IIIA2/IIIB2 self-adjoint → NOT self-adjoint)
4. Verified EmbeddedRK.lean, SDIRK3.lean compile clean
5. Full build: 8050 modules, 0 errors
6. Added BDF5 (5-step, order 5) and BDF6 (6-step, order 6) to MultistepMethods.lean

## Result
SUCCESS — Full build passes with zero errors. Two new BDF methods added. Adjoint.lean and EmbeddedRK.lean now compile (from prior cycle's uncommitted work).

## Dead ends
- None this cycle (all fixes were successful)

## Discovery
- Lobatto IIIA/IIIB 2-stage are NOT self-adjoint (M₀₀ ≠ 0). The original Adjoint.lean incorrectly claimed they were. This was caught because `ring` couldn't close the goals after Lean 4.28's tighter `ring_nf`.
- `Fin.sum_univ_six` and `Fin.sum_univ_seven` don't exist in Mathlib; use `Fin.sum_univ_succ` instead for Fin 6+.

## Suggested next approach
- Check Aristotle results for SDIRK3 sorrys (sdirk3_stiffDecay, sdirk3_poly_ineq)
- Add BDF5/BDF6 zero-stability proofs (complex polynomial root analysis)
- Consider BDF7 NOT zero-stable proof (showing the BDF barrier at order 6)
- A(α)-stability definitions and proofs for BDF family
