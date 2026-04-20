# Cycle 218 Results

## Worked on
`OpenMath/OrderConditions.lean`

- Case C normalization boundary inside `thm_301A_order5`
- `OrderFiveCaseCWitness`
- `order_five_caseC_witness`
- shared Case C target/dispatcher packaging

## Approach
- Read `.prover-state/strategy.md` first and followed the cycle-218 target instead of the stale cycle-217 narrative.
- Did not poll Aristotle: there were no ready Aristotle results to incorporate, and this cycle was theorem-boundary refactoring rather than a new sorry-first batch.
- Converted `OrderFiveCaseCWitness` from `Prop` to `Type`.
- Ported the witness construction to the Case D pattern by proving `order_five_caseC_witness_nonempty` and then defining `order_five_caseC_witness` via `Classical.choice`.
- Added `order_five_caseC_target` and the shared forward/reverse theorem `order_five_caseC_dispatch_shared`.
- Rewrote the reverse Case C dispatcher to build a target proposition and use the shared dispatcher.
- Rewired forward `order5c`, `order5d`, and `order5f` in `thm_301A_order5` to use explicit Case C data witnesses and the shared dispatcher.
- Deleted the three forward-only wrappers:
  - `satisfiesTreeCondition_order_five_caseC_ord22`
  - `satisfiesTreeCondition_order_five_caseC_bushy3`
  - `satisfiesTreeCondition_order_five_caseC_chain3`

## Result
SUCCESS

- No ready Aristotle results were incorporated this cycle.
- The live wrapper refactor from cycle 217 was already present on `main`; this cycle moved past wrappers to a genuinely shared Case C boundary.
- `OrderFiveCaseCWitness` is now data in `Type`, not `Prop`.
- `order_five_caseC_target` and a shared forward/reverse dispatcher were added.
- All three forward wrapper lemmas were deleted.
- Forward and reverse Case C now both route through the same dispatcher.

## Dead ends
- A direct theorem returning `OrderFiveCaseCWitness c₁ c₂` failed because theorem codomains must be propositions.
- A constructive proof of the data-valued witness also failed on `Prop` elimination (`Or`/`order_three_cases`) into `Type`.
- The correct fix was to mirror Case D exactly: prove `Nonempty (OrderFiveCaseCWitness c₁ c₂)` and then choose a witness noncomputably.

## Discovery
- The Case C refactor ports cleanly once the witness selection is phrased as `Nonempty` plus `Classical.choice`.
- The previous blocker from `.prover-state/issues/order5_caseC_forward_dispatch_gap.md` was exactly the `Prop`-valued witness boundary; no extra wrappers are needed after the data-witness conversion.

## Suggested next approach
- Theorem-boundary cleanup for Theorem 301A rooted-tree infrastructure is now more uniform across Case C and Case D.
- Future work should continue from the live repository state rather than the stale wrapper-focused cycle-217 narrative.

## Verification
- Ran `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderConditions.lean`
- Ran `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build`
