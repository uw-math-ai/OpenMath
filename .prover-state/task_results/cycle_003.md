# Cycle 003 Results

## Worked on
Section 1.2: Linear Multistep Methods. Created `OpenMath/MultistepMethods.lean` with the LMM framework: structure definition, characteristic polynomials, consistency conditions, and four standard methods with full proofs.

## Approach
1. Cycle 2 had already completed Theorem 213A (all sorrys closed). Verified it compiles.
2. Advanced to next plan target: Section 1.2 (Linear Multistep Methods).
3. Sorry-first workflow: wrote full skeleton with 14 sorrys, verified compilation, then closed all sorrys.
4. Used `lean_multi_attempt` to find optimal proof terms for each sorry.

## Result
**SUCCESS — Tier 3 (all sorrys closed)**

Created `OpenMath/MultistepMethods.lean` with 0 sorry in committed code:

### Definitions
- `LMM s`: Structure for s-step linear multistep methods (α, β coefficients, normalized α_s = 1)
- `LMM.rho`: First characteristic polynomial ρ(ξ) = ∑ α_j ξ^j
- `LMM.sigma`: Second characteristic polynomial σ(ξ) = ∑ β_j ξ^j
- `LMM.IsConsistent`: Consistency (ρ(1) = 0 and ρ'(1) = σ(1))
- `LMM.IsExplicit` / `LMM.IsImplicit`: Classification by β_s = 0 vs β_s ≠ 0

### Standard Methods (all fully defined)
- `forwardEuler`: α = [-1, 1], β = [1, 0]
- `backwardEuler`: α = [-1, 1], β = [0, 1]
- `trapezoidalRule`: α = [-1, 1], β = [1/2, 1/2]
- `adamsBashforth2`: α = [0, -1, 1], β = [-1/2, 3/2, 0]

### Theorems (all proved, verified via lean_verify)
- `LMM.rho_one`: ρ(1) = ∑ α_j
- `LMM.sigma_one`: σ(1) = ∑ β_j
- `forwardEuler_consistent`, `backwardEuler_consistent`, `trapezoidalRule_consistent`, `adamsBashforth2_consistent`
- `forwardEuler_explicit`, `adamsBashforth2_explicit`
- `backwardEuler_implicit`, `trapezoidalRule_implicit`

All use standard axioms only (propext, Classical.choice, Quot.sound).

## Dead ends
- `lean_multi_attempt` initially failed with "unexpected identifier; expected 'lemma'" errors when sorry files had many unresolved sorrys. Resolved by fixing earlier sorrys first, then running multi_attempt.
- `native_decide` and `decide` don't work for ℝ equalities (not decidable). Used `simp [Fin.last]` for normalization proofs.
- `simp` alone can't close `1 = 2⁻¹ + 2⁻¹` (trapezoidal) or `-1 + 2 = -1/2 + 3/2` (AB2). Need `norm_num` for fractional arithmetic.

## Discovery
- `Fin.sum_univ_two` and `Fin.sum_univ_three` are the key simp lemmas for reducing sums over Fin 2 and Fin 3.
- `simp [Fin.last]` closes `![-1, 1] (Fin.last 1) = 1` without needing `rfl`.
- `constructor <;> simp [LMM.rho, LMM.sigma, method_name, Fin.sum_univ_N]` is the pattern for consistency proofs. Add `<;> norm_num` when fractions are involved.
- `simp [LMM.IsExplicit, method_name, Fin.last]` closes explicit/implicit classification.

## Suggested next approach
- Define **zero-stability** (root condition on ρ(ξ)): all roots in the closed unit disk, simple roots on the boundary.
- Prove forward Euler, backward Euler, trapezoidal, and AB2 are zero-stable.
- State the **Dahlquist equivalence theorem**: consistency + zero-stability ⟺ convergence.
- Alternatively, define the **order** of an LMM via the error constants C_q and prove order of the four standard methods.
