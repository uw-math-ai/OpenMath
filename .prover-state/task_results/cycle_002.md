# Cycle 002 Results

## Worked on
Theorem 213A: Convergence of the Euler method. Created `OpenMath/EulerConvergence.lean` with 5 theorems proving that the Gronwall error bound is O(h) and converges to zero as h -> 0.

## Approach
1. Created sorry skeleton with all 5 theorems (Part 1: algebraic, Part 2: limits).
2. Closed sorrys in priority order using Lean LSP tools (`lean_multi_attempt`, `lean_goal`).
3. Used `gronwallBound_K0` and `gronwallBound_of_K_ne_0` from Mathlib as primary proof tools.
4. Case-split on L = 0 vs L > 0 throughout.

## Result
**SUCCESS — Tier 3 (all sorrys closed)**

All 5 theorems fully proved, no sorry in committed code:
- `gronwallBound_linear_in_h_pos`: gronwallBound 0 L (M*h) T = M/L * (exp(LT)-1) * h
- `gronwallBound_linear_in_h_zero`: gronwallBound 0 0 (M*h) T = M*T*h
- `euler_convergence_order1`: exists K >= 0 s.t. gronwallBound 0 L (M*h) T <= K*h
- `gronwallBound_tendsto_zero_seq`: delta_n -> 0, eps_n -> 0 implies gronwallBound -> 0
- `euler_convergence_tendsto`: corollary for Euler method convergence

Verified via `lean_verify`: only standard axioms (propext, Classical.choice, Quot.sound).

## Dead ends
- `rw` inside `fun h hh => by` block failed to find the pattern; used `exact le_of_eq` instead.
- `Tendsto.const_mul` produces `nhds (M * 0)` not `nhds 0`; needed `simpa using` to close the gap.
- Initial `lake build` failed due to broken NVMe symlinks; fixed by running `lake exe cache get` then `lake build OpenMath.Basic`.

## Discovery
- `gronwallBound_K0` and `gronwallBound_of_K_ne_0` unfold cleanly with `simp [...]; ring`.
- `simp_rw` is essential for rewriting inside lambdas (vs `rw` which fails).
- `Tendsto` arithmetic: `hf.add`, `hf.mul_const`, `hf.div_const` compose nicely; use `simpa using` to normalize `M * 0 = 0`.
- Build setup: need `lake build OpenMath.Basic` before `lake env lean` on dependent files if no oleans exist.

## Suggested next approach
- Next target: Theorem 221A (multistep methods) or begin formalizing the ODE/Euler iteration infrastructure needed for connecting 212A/213A to actual numerical schemes.
- The abstract Gronwall bound toolkit (212A + 213A) is now complete. Future work should build on `gronwallBound` directly.
