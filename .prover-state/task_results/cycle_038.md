# Cycle 038 Results

## Worked on
- Investigated `uniformly_bounded_tupleSucc_iterates` (spectral bound sorry in DahlquistEquivalence.lean)
- Formalized Radau IIA 2-stage method in `OpenMath/StiffEquations.lean`
- Fixed existing broken proofs in StiffEquations.lean (Mathlib API drift)

## Approach

### Spectral bound investigation
Systematically searched Mathlib for eigenspace decomposition infrastructure.
Found 6 relevant lemmas (`iSup_maxGenEigenspace_eq_top`, `hasEigenvalue_iff_isRoot_charpoly`,
`isNilpotent_restrict_genEigenspace_nat`, etc.) but identified 3 critical gaps:
1. Connection between `LinearRecurrence.charPoly` and `LinearMap.charpoly` for `tupleSucc`
2. Eigenvalue bounds → operator power bounds (binomial theorem for endomorphisms)
3. `IsZeroStable` → eigenvalue characterization

Wrote detailed issue file `.prover-state/issues/spectral_bound_tupleSucc.md`.
Pivoted to Option B per strategy.

### Radau IIA formalization (new material)
Defined the full Radau IIA 2-stage method and proved all key properties:

1. **Definition**: `rkRadauIIA2` — Butcher tableau with A = [[5/12, -1/12], [3/4, 1/4]], b = [3/4, 1/4], c = [1/3, 1]
2. **Consistency**: `rkRadauIIA2_consistent` — weights sum to 1, row sums match c
3. **Order 3**: `rkRadauIIA2_order3` — satisfies all order 3 conditions
4. **Not order 4**: `rkRadauIIA2_not_order4` — ∑bᵢcᵢ³ = 5/18 ≠ 1/4
5. **Non-negative weights**: `rkRadauIIA2_nonNegWeights`
6. **Algebraic stability**: `rkRadauIIA2_algStable` — M = (1/16)·[[1,-1],[-1,1]] is PSD
7. **Stability function**: `radauIIA2StabilityFn` = (1+z/3)/(1-2z/3+z²/6)
8. **A-stability**: `radauIIA2_aStable` — |R(z)| ≤ 1 for Re(z) ≤ 0, via normSq inequality
9. **Stiff decay**: `radauIIA2_stiffDecay` — R(x) → 0 as x → -∞
10. **L-stability**: `radauIIA2_lStable` — A-stable + stiff decay

### Existing proof fixes
Fixed proofs broken by Mathlib API drift:
- `rkImplicitEuler_stiffDecay`: `inv_lt_comm₀` approach for division inequality
- `rkImplicitMidpoint_stabilityFn1_tendsto`: Complex cast rewrites with `sub_div'`
- `gl2StabilityFn_tendsto_one`: `one_sub_div` for complex rewrite, fixed `linarith` division issues

## Result
**SUCCESS** — 10 new sorry-free theorems about Radau IIA 2-stage method. All existing proofs
in StiffEquations.lean also fixed. File compiles cleanly. All key theorems verified with
`lean_verify` (only standard axioms).

## Dead ends
- `field_simp; ring` fails when `field_simp` introduces `⁻¹` terms that `ring` can't handle.
  Fix: use `sub_div'` or `one_sub_div` to restructure before `ring`.
- `linarith` can't handle `-a/ε = -(a/ε)` — needs explicit `have : -a/ε = -(a/ε) := by ring`.
- `positivity` can't prove `0 < x^2/k` even when `x ≠ 0` — use `nlinarith [sq_nonneg x]`.
- `div_le_div_of_nonneg_left` first arg needs `0 ≤ a` (weak), not `0 < a` (strict).

## Discovery
- `simp [radauIIA2Num]` and `simp [gl2Denom]` etc. fully close `f(↑x) = ↑(...)` goals
  (the `push_cast; ring` is unnecessary after simp unfolds the definition).
- `one_sub_div hne` rewrites `1 - a/b = (b-a)/b`, much cleaner than `sub_div'` for ℂ goals.
- The normSq approach for A-stability works well: reduce to real normSq computation,
  then `nlinarith` with squared terms.

## Suggested next approach
- Continue Chapter 4: stiff equations with SDIRK methods, BDF stability analysis
- Or move to Section 2.3: collocation methods — define collocation RK, prove order conditions
- The spectral bound sorry remains; see `.prover-state/issues/spectral_bound_tupleSucc.md`
