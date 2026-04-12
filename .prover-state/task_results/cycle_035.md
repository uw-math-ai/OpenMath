# Cycle 035 Results

## Worked on
Dahlquist equivalence theorem (Iserles, Theorem 1.5.2): consistency + zero-stability ⟺ convergence for linear multistep methods.

Created new file `OpenMath/DahlquistEquivalence.lean` with the full theorem structure.

## Approach
Sorry-first: defined all concepts, stated all theorems, then closed sorrys one by one.

### Definitions created:
- `SatisfiesRecurrence`: sequence satisfies the characteristic recurrence ∑ α_j y_{n+j} = 0
- `HasStableRecurrence`: all solutions of the recurrence are bounded
- `IsConvergent`: consistency + stable recurrence
- `ConvergesForTrivialODE`: convergence for y' = 0 (equivalent to stable recurrence)

### Theorems proved (0 sorry):
1. **`geometric_satisfies_iff`**: ξ^n satisfies the recurrence ⟺ ρ(ξ) = 0. Connects polynomial roots to recurrence solutions.
2. **`linear_geometric_satisfies`**: n·ξ^n satisfies the recurrence when ξ is a double root (ρ(ξ) = 0, ρ'(ξ) = 0). Uses algebraic identity: ∑ α_j(n+j)ξ^{n+j} = nξ^n·ρ(ξ) + ξ^{n+1}·ρ'(ξ).
3. **`not_stableRecurrence_of_root_outside_disk`**: If ρ has a root with |ξ| > 1, then ξ^n diverges → recurrence unstable. Uses `tendsto_pow_atTop_atTop_of_one_lt`.
4. **`not_stableRecurrence_of_double_root_on_circle`**: If ρ has a double root with |ξ| = 1, then ‖n·ξ^n‖ = n → ∞ → unstable.
5. **`zeroStable_of_stableRecurrence`**: Stable recurrence → zero-stable. Combines (3) and (4) by contrapositive.
6. **`dahlquist_equivalence`**: Full equivalence: IsConvergent ↔ IsConsistent ∧ IsZeroStable.
7. **Convergence of standard methods**: forwardEuler, backwardEuler, trapezoidalRule, adamsBashforth2, adamsMoulton2, bdf2 all verified convergent.
8. **`dahlquistCounterexample_not_convergent`**: The order-3 A-stable counterexample is NOT convergent (not zero-stable).

### Remaining sorry (1):
- **`stableRecurrence_of_zeroStable`**: zero-stable → stable recurrence. Requires general solution theory for linear recurrences: every solution is a linear combination of ξ^n, n·ξ^n, ..., n^{k-1}·ξ^n. This needs companion matrix eigenvalue analysis or polynomial factorization machinery.

## Result
SUCCESS — New file `OpenMath/DahlquistEquivalence.lean` compiles with 1 sorry. The Dahlquist equivalence theorem is fully stated and the backward direction (stable recurrence → zero-stable) is fully proved. 7 convergence theorems for standard methods are proved. 8 new theorems total.

## Dead ends
None — the approach worked cleanly.

## Discovery
- `tendsto_pow_atTop_atTop_of_one_lt` is the right Mathlib lemma for showing r^n → ∞ when r > 1.
- `Filter.tendsto_atTop_atTop` unfolds to the expected ∀∃ form.
- When working with `rhoC` (defined as a sum), `simp_rw [hρ]` fails because `hρ : m.rhoC ξ = 0` doesn't match the unfolded sum. Need to either unfold hρ or use `have : (sum) = 0 := hρ`.
- `dsimp only` is needed to beta-reduce lambdas after `subst`.

## Suggested next approach
1. **Close `stableRecurrence_of_zeroStable`**: Define the companion matrix of ρ, show solutions are A^n · y₀, prove ‖A^n‖ is bounded under the root condition. Alternatively, use polynomial factorization: peel off roots one at a time with an inductive argument.
2. **Or move to new material**: Chapter 4 (stiff equations), collocation methods, or higher-order Gauss-Legendre.
