# Strategy — Cycle 91

## Status snapshot

| # | File | Line | Theorem / sorry | Priority |
|---|------|------|-----------------|----------|
| — | MultistepMethods.lean | — | **SORRY-FREE** | — |

DahlquistEquivalence.lean: **sorry-free**.
SpectralBound.lean: **sorry-free**.

Total sorrys: **0**.

## Cycle 90 outcome

Both remaining sorrys closed:
1. `reversed_poly_C3_condition` — C₃ reversed-polynomial identity proved by mirroring C₂ template with `pow_one` normalization for V₂.
2. `continuousOn_Gtilde_closedBall` — integrated Aristotle's proof with `h_unit` hypothesis (only unit-circle root of ρ is 1). Added helper `rhoCRev_ne_zero_of_closedBall_ne_one`. Propagated `h_unit` to `order_ge_three_not_aStable_core`, `order_ge_three_not_aStable`, `dahlquist_second_barrier`.

All theorems axiom-verified (propext, Classical.choice, Quot.sound only). File compiles with zero errors.

## What's next

With MultistepMethods.lean sorry-free, the Dahlquist barrier formalization is complete. Potential next tasks:
1. **Clean up linter warnings** — many unused simp args in MultistepMethods.lean.
2. **Document the `h_unit` hypothesis** — update extraction/formalization_data entities for theorems that gained this hypothesis.
3. **Continue textbook formalization** — check plan.md for next chapter targets.
4. **BDF zero-stability** — BDF5/BDF6 zero-stability proofs still pending (4th/5th degree polynomial root bounds).
5. **Extend RK formalization** — ExplicitRK.lean, OrderBarriers.lean, Symmetry.lean, Adjoint.lean are complete; consider implicit RK infrastructure.
