# Issue: uniformly_bounded_tupleSucc_iterates requires eigenspace decomposition infrastructure

## Blocker
The sorry at `OpenMath/DahlquistEquivalence.lean:284` requires proving that under
zero-stability (root condition), the companion operator `tupleSucc` has uniformly
bounded iterates: ‖tupleSucc^n(v)‖ ≤ M·‖v‖ for all n, v.

This is the standard spectral bound: spectral radius ≤ 1 with semisimple unit
eigenvalues implies bounded operator powers. Mathlib does NOT have this theorem.

## Context

```lean
theorem uniformly_bounded_tupleSucc_iterates (m : LMM s) (hzs : m.IsZeroStable) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (v : Fin s → ℂ),
      ‖(m.toLinearRecurrence.tupleSucc^[n]) v‖ ≤ M * ‖v‖ := by
  sorry
```

## What was tried

### Cycle 37 investigation
Systematically searched Mathlib for usable infrastructure. Found:

1. **`Module.End.iSup_maxGenEigenspace_eq_top`** (Triangularizable.lean):
   Over an algebraically closed field, V = ⨆ maxGenEigenspace(f, μ). ✓ Available.

2. **`Module.End.hasEigenvalue_iff_isRoot_charpoly`** (Eigenspace/Charpoly.lean):
   Eigenvalues = roots of characteristic polynomial. ✓ Available.

3. **`Module.End.isNilpotent_restrict_genEigenspace_nat`** (Eigenspace/Basic.lean):
   f - μ is nilpotent on generalized eigenspace. ✓ Available.

4. **`Module.End.independent_maxGenEigenspace`** (Eigenspace/Basic.lean):
   Generalized eigenspaces are independent. ✓ Available.

5. **`LinearMap.finrank_maxGenEigenspace_eq`** (Eigs.lean):
   dim(maxGenEigenspace μ) = rootMultiplicity μ. ✓ Available.

6. **Gelfand formula** (GelfandFormula.lean):
   spectralRadius = lim ‖a^n‖^{1/n}. ✓ Available but insufficient (doesn't give uniform bound).

### What's missing (the gaps)

**Gap 1**: Connection between `LinearRecurrence.charPoly` and `LinearMap.charpoly` for `tupleSucc`.
- `LinearRecurrence.charPoly` is defined as `X^s - ∑ c_i X^i`.
- `LinearMap.charpoly` is `det(X·I - f)` via the matrix representation.
- Need to prove these are equal (or have the same roots) for `tupleSucc`.
- This requires choosing a basis for `Fin s → ℂ` and computing the matrix of `tupleSucc`.

**Gap 2**: From eigenvalue bounds to operator power bounds.
- Need: eigenvalues have |μ| ≤ 1 with semisimple unit eigenvalues → ‖f^n‖ ≤ M.
- Proof sketch: decompose V = ⨁ maxGenEigenspace(f, μ). On each:
  - f = μ·id + N where N nilpotent (N^d = 0 for d = dim)
  - f^n = ∑_{k<d} C(n,k) μ^{n-k} N^k
  - If |μ| < 1: exponential decay dominates polynomial growth → bounded
  - If |μ| = 1 and semisimple: dim(genEigenspace) = 1 (simple root), so N = 0, f^n = μ^n·id
- Need: binomial theorem for endomorphisms, norm bounds on each piece,
  combining via direct sum projection norms.

**Gap 3**: `IsZeroStable` uses roots of `rhoC` (a sum formula), while Mathlib eigenspace
theory uses `LinearMap.charpoly`. Need to relate these two characterizations.

### Approaches considered but rejected

1. **Cayley-Hamilton alone**: T^n = r_n(T) where r_n = X^n mod charPoly. Bounding coefficients
   of r_n requires showing sequences satisfying the same recurrence are bounded — circular.

2. **Gelfand formula**: Gives spectralRadius = lim ‖T^n‖^{1/n}, but spectral radius = 1
   does NOT imply ‖T^n‖ ≤ C without the semisimplicity condition.

3. **Banach-Steinhaus**: Could derive uniform bound from pointwise boundedness, but proving
   pointwise boundedness requires solution boundedness — the thing we're trying to prove.

## Possible solutions

### Path A: Build the full proof (estimated 3-5 cycles)
1. **Cycle N**: Prove `tupleSucc` matrix = companion matrix, and its `charpoly` = `charPoly`.
2. **Cycle N+1**: Prove eigenvalue bound lemma: eigenvalues of tupleSucc satisfy |μ| ≤ 1 with
   simple unit roots (using Gap 1 + IsZeroStable).
3. **Cycle N+2**: Prove bounded powers on each generalized eigenspace (binomial expansion + norm bounds).
4. **Cycle N+3**: Combine via direct sum decomposition (iSup_maxGenEigenspace_eq_top + projections).

### Path B: Restructure the proof to avoid operator norm bound
- Prove `stableRecurrence_of_zeroStable` directly using the explicit solution formula
  (general solution = linear combination of n^k · ξ^n terms).
- Still needs the completeness of the solution basis, which requires similar eigenspace infrastructure.

### Path C: Accept as axiom
- The mathematical content is correct and standard.
- Leave the sorry with a detailed docstring explaining the mathematical argument.
- Focus formalization effort on new theorems where Mathlib gaps are smaller.

## Recommendation
Path A is the most principled but requires sustained effort across multiple cycles.
Path C is pragmatic — the Dahlquist equivalence theorem IS correctly formalized modulo
this one well-understood spectral theory fact. Prioritize Path A when/if Mathlib's
eigenspace infrastructure improves or when a dedicated eigenvalue theory cycle is planned.
