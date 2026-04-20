# Cycle 217 Results

## Worked on
Forward Case C branches of `thm_301A_order5` in `OpenMath/OrderConditions.lean`, specifically `order5c`, `order5d`, and `order5f`.

## Approach
Re-read the existing Case C witness/dispatcher infrastructure and the three theorem-boundary branches in `thm_301A_order5`.

There were no ready Aristotle results to incorporate this cycle, and the planner explicitly said not to poll stale jobs again. The repository also had no `sorry` in `OpenMath/`, so I did not create a new Aristotle batch for this scoped refactor.

I first attempted to add a shared forward/reverse Case C dispatcher over `OrderFiveCaseCWitness` so the forward branches could route through the same witness boundary as the reverse direction. That ran into Lean's Prop-indexed elimination restriction when trying to package a branch-specific theorem target over `OrderFiveCaseCWitness`.

I then kept the file compiling and replaced the forward theorem-boundary uses with small Case C wrappers:

- `satisfiesTreeCondition_order_five_caseC_ord22`
- `satisfiesTreeCondition_order_five_caseC_bushy3`
- `satisfiesTreeCondition_order_five_caseC_chain3`

These wrappers package the concrete Case C families directly as `order5c`, `order5d`, and `order5f`, and the forward branches in `thm_301A_order5` now call those wrappers instead of calling the family-specific ordered/canonical theorems inline.

## Result
FAILED

The scoped theorem-boundary cleanup made real progress in `OpenMath/OrderConditions.lean`:

- `order5c` no longer directly calls `satisfiesTreeCondition_order_five_22` inside `thm_301A_order5`
- `order5d` no longer directly calls `satisfiesTreeCondition_order_five_bushy3_canonical` inside `thm_301A_order5`
- `order5f` no longer directly calls `satisfiesTreeCondition_order_five_chain3_canonical` inside `thm_301A_order5`

However, the forward branches do not yet route through `satisfiesTreeCondition_order_five_caseC`. The reverse Case C branch still uses the shared dispatcher, but the forward direction still needs an additional abstraction step to make that boundary genuinely shared.

## Dead ends
Tried to define a shared theorem that would map

- `tab.satisfiesTreeCondition (.node [c₁, c₂])`

to a branch-specific target selected by `OrderFiveCaseCWitness c₁ c₂`, and conversely.

This failed because the target proposition depended on a `Prop`-valued indexed witness, and Lean rejected the elimination with `nested.lean.propRecLargeElim`.

## Discovery
The current shared Case C API is sufficient for the reverse direction:

- `OrderFiveCaseCWitness`
- `order_five_caseC_witness`
- `satisfiesTreeCondition_order_five_caseC`

but it is not sufficient for the forward direction, because the forward proof needs a witness-indexed theorem target like `order5c` versus `order5d` versus `order5f`, and that packaging currently collides with Lean's elimination restrictions on the Prop-indexed witness.

## Suggested next approach
Add one forward-direction helper that avoids dependent elimination over `OrderFiveCaseCWitness` in `Prop`.

Likely options:

1. use a non-dependent Case C target encoding that does not pattern-match on the witness in the codomain,
2. or refactor `OrderFiveCaseCWitness` / its forward target packaging so Lean can eliminate without hitting `propRecLargeElim`.

The focused blocker is recorded in `.prover-state/issues/order5_caseC_forward_dispatch_gap.md`.

## Verification
Ran:

- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderConditions.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build`
