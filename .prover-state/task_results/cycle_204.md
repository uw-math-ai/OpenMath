# Cycle 204 Results

## Worked on
Nested unary order-5 `via_via_bushy3` / `via_via_chain3` infrastructure in
`OpenMath/OrderConditions.lean`.

## Approach
Added family-level transport helpers for the remaining nested unary order-5
families so the final tree-condition lemmas route through one canonical proof
path per family.

New elementary-weight transport helpers:
`ew_of_order_five_via_via_bushy3_eq_of_childrenBag_eq`
`ew_of_order_five_via_via_chain3_eq_of_childrenBag_eq`

New density transport helpers:
`density_of_order_five_via_via_bushy3_eq_of_childrenBag_eq`
`density_of_order_five_via_via_chain3_eq_of_childrenBag_eq`

New tree-condition transport helpers:
`satisfiesTreeCondition_order_five_via_via_bushy3_eq_of_childrenBag_eq`
`satisfiesTreeCondition_order_five_via_via_chain3_eq_of_childrenBag_eq`

Rewrote the final family theorems
`satisfiesTreeCondition_order_five_via_via_bushy3` and
`satisfiesTreeCondition_order_five_via_via_chain3`
to route through the new transport helpers instead of carrying their own direct
`elementaryWeight`/density proof scripts.

No new `sorry` was introduced, so per the cycle strategy this was not an
Aristotle cycle and Aristotle was skipped.

## Result
SUCCESS. Both nested unary order-5 families now have family-level transport
helpers, and the final theorems route through those helpers instead of proving
the final condition directly from ordered witness data.

## Dead ends
The first version of the new `elementaryWeight` transport lemmas tried to rewrite
both nested singleton layers in one step. Lean only exposed the inner
`elementaryWeight (.node [...])` terms after rewriting the middle unary layer, so
the proofs were changed to introduce an intermediate pointwise `hew` lemma for
the middle singleton node and then rewrite the outer sum with that lemma.

## Discovery
For these nested unary families, the practical transport boundary is still a
family-level helper around the full unary-unary tree. The helper packages the
inner `childrenBag` transport, then reuses the existing canonical direct theorem
for the fully normalized witness.

## Suggested next approach
Apply the same canonical-plus-transport packaging to any remaining rooted-tree
families that still expose direct ordered witness scripts in their final theorem
statement, but keep the refactor local to `OrderConditions.lean`.

## Verification
Ran:

```bash
export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH
lake env lean OpenMath/RootedTree.lean
lake env lean OpenMath/OrderConditions.lean
```

Both commands completed successfully. `OpenMath/OrderConditions.lean` still
emits pre-existing unused-`simp` warnings unrelated to this cycle.
