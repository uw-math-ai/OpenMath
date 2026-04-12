# Cycle 044 Results

## Worked on
1. **SDIRK 2-stage method** (`OpenMath/SDIRK.lean`) — new file
2. **Radau IIA 3-stage method** (`OpenMath/RadauIIA3.lean`) — new file
3. **Collocation methods & simplifying assumptions** (`OpenMath/Collocation.lean`) — new file

## Approach
- Sorry-first: wrote full proof structure with sorrys, compiled, then closed all sorrys.
- Used LSP tools (`lean_goal`, `lean_multi_attempt`) to debug tactic failures.
- For algebraic stability of RadauIIA3, used SOS (sum-of-squares) decomposition to prove positive semidefiniteness of the algebraic stability matrix.

## Result
**SUCCESS** — Three new sorry-free files committed.

### SDIRK.lean (~307 lines)
- `rkSDIRK2`: 2-stage SDIRK method definition (λ = 1 - √2/2)
- Consistency, order 2 (not order 3), non-negative weights
- Stability function, A-stability, stiff decay, L-stability
- `rkSDIRK2_not_algStable`: SDIRK2 is NOT algebraically stable (M₁₁ < 0)

### RadauIIA3.lean (~314 lines)
- `rkRadauIIA3`: 3-stage Radau IIA method (nodes 2/5-√6/10, 2/5+√6/10, 1)
- Consistency, order 4 (verified all 8 conditions), non-negative weights
- Stability function R(z) = P(z)/Q(z), A-stability, stiff decay, L-stability
- `rkRadauIIA3_algStable`: Algebraic stability via SOS decomposition
  (key identity: 324(7-2√6)·Q(v) = ((7-2√6)v₀ - 5v₁ + 2(√6-1)v₂)²)

### Collocation.lean (~250 lines)
- **Simplifying assumptions B(p), C(q), D(r)** — definitions and monotonicity
- **Equivalences**: C(1) ↔ row-sum condition, B(1) ↔ order1, B(1)∧C(1) ↔ consistency
- **Order from B+C**: B(1)→order≥1, B(2)∧C(1)→order≥2, B(3)∧C(2)→order≥3, B(4)∧C(3)→order≥4
- **Verification**: backward Euler B(1)/C(1), implicit midpoint B(2)/C(1), GL2 B(4)/C(2)

## Dead ends
- `λ_` as variable name: Lean 4 keyword conflict. Fixed by using `sdirk2Lambda` directly.
- `ext` for Complex: `ext <;> simp` no longer works; need `apply Complex.ext`.
- RadauIIA3 algebraic stability: `nlinarith` alone can't handle the 3×3 PSD matrix.
  SOS decomposition with explicit hint `sq_nonneg (...)` was needed.
- `set` with ↑-casts: `set lam := sdirk2Lambda` doesn't replace `↑sdirk2Lambda` inside
  Complex.ofReal casts after simp unfolds definitions.
- Collocation `ext j` for ℝ: `congr 1; ext j; ring` fails when `congr` produces ℝ equality
  instead of function equality. Fixed with `Finset.sum_congr` approach.

## Discovery
- The order-from-B+C proofs are clean and general: they work for arbitrary s-stage methods.
  The key pattern is: factor summand via `ring`, apply `Finset.sum_congr` or `← Finset.mul_sum`,
  then chain B and C conditions.
- SDIRK2 is NOT algebraically stable despite being L-stable. The diagonal entry
  M₁₁ = (1-λ)(3λ-1) is negative because λ ≈ 0.293 < 1/3.
- `interval_cases k` is very effective for proving B(p)/C(q) for specific methods.

## Suggested next approach
- **Extend collocation**: prove that Gauss nodes give B(2s) and C(s), connecting to GL2 order 4.
- **More stiff methods**: SDIRK3 (3-stage, order 3, L-stable), or TR-BDF2.
- **BDF methods**: formalize A(α)-stability for BDF methods (Section 4.5).
- **Collocation→RK correspondence**: define Lagrange interpolation and prove Theorem 2.4
  (aᵢⱼ = ∫₀^{cᵢ} ℓⱼ(τ) dτ gives C(s)).
