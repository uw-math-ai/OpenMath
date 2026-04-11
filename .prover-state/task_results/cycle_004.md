# Cycle 004 Results

## Worked on
Order of linear multistep methods (Option B from strategy): definitions, linking theorems, and order proofs for all four standard methods.

## Approach
1. Defined `LMM.orderCondVal q` — the q-th order condition value (unnormalized error constant):
   V_q = ∑_j j^q α_j - q · ∑_j j^{q-1} β_j
2. Defined `LMM.HasOrder p` — a structure requiring V_0 = ... = V_p = 0 and V_{p+1} ≠ 0.
3. Proved linking theorems connecting order conditions to existing definitions (ρ, σ, consistency).
4. Proved order for all four standard methods using `interval_cases`, `simp`, and `norm_num`.
5. Used sorry-first workflow: wrote full structure with sorry, compiled, then closed all sorrys.

## Result
SUCCESS — All 8 sorrys closed. Zero sorry in committed code.

### New definitions
- `LMM.orderCondVal` — q-th order condition value
- `LMM.HasOrder` — order p structure

### New theorems (all fully proved)
- `LMM.orderCondVal_zero` — V_0 = ρ(1)
- `LMM.orderCondVal_one` — V_1 = ρ'(1) - σ(1)
- `LMM.isConsistent_iff_orderCond` — consistency ↔ V_0 = 0 ∧ V_1 = 0
- `LMM.HasOrder.isConsistent` — order p ≥ 1 implies consistency
- `forwardEuler_order_one` — Forward Euler has order 1
- `backwardEuler_order_one` — Backward Euler has order 1
- `trapezoidalRule_order_two` — Trapezoidal rule has order 2
- `adamsBashforth2_order_two` — Adams–Bashforth 2-step has order 2

## Dead ends
None — the proofs were straightforward with the computational approach.

## Discovery
- `interval_cases` + `simp` + `norm_num` is highly effective for order condition proofs on concrete methods.
- The unified formula V_q = ∑ j^q α_j - q · ∑ j^{q-1} β_j works for all q ≥ 0 thanks to ℕ subtraction (0-1=0) and the zero coefficient at q=0.
- `all_goals simp [...]; all_goals norm_num` avoids lint warnings about unnecessary `<;>` when simp closes some but not all goals.

## Suggested next approach
- **Zero-stability** (Option A): Define using Mathlib's `Polynomial.IsRoot` and `Polynomial.roots`. Prove zero-stability for the four standard methods.
- **Dahlquist equivalence theorem** (Option C): State as sorry — consistency + zero-stability ⟺ convergence.
- **Higher-order methods**: Define Adams–Bashforth 3-step, Adams–Moulton methods, or BDF methods and prove their order.
