# Cycle 005 Results

## Worked on
Zero-stability of linear multistep methods (Option A from strategy): definitions of complex characteristic polynomial, its derivative, zero-stability, and proofs for all four standard methods.

## Approach
1. Defined `LMM.rhoC` — the first characteristic polynomial evaluated over ℂ (casting α coefficients from ℝ to ℂ).
2. Defined `LMM.rhoCDeriv` — the formal derivative of ρ over ℂ.
3. Defined `LMM.IsZeroStable` — structure requiring all roots of ρ in the closed unit disk (‖ξ‖ ≤ 1) and simplicity of unit-circle roots (ρ'(ξ) ≠ 0).
4. Proved zero-stability for all four standard methods:
   - 1-step methods (forwardEuler, backwardEuler, trapezoidalRule): ρ(ξ) = ξ - 1, sole root ξ = 1, derivative is constant (nonzero).
   - AB2: ρ(ξ) = ξ² - ξ = ξ(ξ - 1), roots at 0 and 1, both in unit disk, ρ'(1) = 1 ≠ 0.
5. Used sorry-first workflow: wrote full structure with sorry, compiled, then closed all sorrys.

## Result
SUCCESS — All 5 sorrys closed (3 for 1-step roots_in_disk, 2 for AB2). Zero sorry in committed code.

### New definitions
- `LMM.rhoC` — first characteristic polynomial over ℂ
- `LMM.rhoCDeriv` — formal derivative of ρ over ℂ
- `LMM.IsZeroStable` — zero-stability (root condition)

### New theorems (all fully proved)
- `forwardEuler_zeroStable` — Forward Euler is zero-stable
- `backwardEuler_zeroStable` — Backward Euler is zero-stable
- `trapezoidalRule_zeroStable` — Trapezoidal rule is zero-stable
- `adamsBashforth2_zeroStable` — Adams–Bashforth 2-step is zero-stable

## Dead ends
- `Complex.abs` no longer exists in Lean 4 Mathlib; use `‖·‖` (norm) instead.
- `linarith` does not work over ℂ (not linearly ordered); `linear_combination` is the correct tool for algebraic identities over ℂ.

## Discovery
- `linear_combination` is essential for complex-valued polynomial root proofs — it handles ring identities over ℂ that `linarith` cannot.
- For the 1-step methods, `simp` alone closes the `unit_roots_simple` goal because the derivative reduces to a nonzero constant.
- For AB2, factoring `ξ(ξ - 1) = 0` via `mul_eq_zero` followed by case analysis is clean and efficient.
- The sorry-first → `lean_multi_attempt` workflow continues to be highly effective.

## Suggested next approach
- **Dahlquist equivalence theorem** (Option C): State consistency + zero-stability ⟺ convergence (with sorry proof). This is the main structural theorem of Section 1.5.
- **Higher-order methods**: Define Adams–Bashforth 3-step, Adams–Moulton methods, or BDF methods and prove their order and zero-stability.
- **A-stability**: Define A-stability (all roots of the stability polynomial in the left half-plane) and prove it for the trapezoidal rule.
