# Cycle 190 Results

## Worked on
- Inspected Aristotle bundle `a4039d71-e5db-49e8-b91a-f227d1bbca8b` first, limited to the required summary and `Legendre.lean`.
- Refactored the order-5 mixed pair in `OpenMath/OrderConditions.lean`, with `satisfiesTreeCondition_order_five_via_mixed12` kept as the canonical theorem.

## Approach
- Triaged the Aristotle output against the current in-repo `OpenMath/Legendre.lean`.
- Read only the focused mixed-pair area around `ew_of_order_five_via_mixed12`, `ew_of_order_five_via_mixed21`, `satisfiesTreeCondition_order_five_via_mixed12`, and `satisfiesTreeCondition_order_five_via_mixed21`.
- Checked existing bag-facing transport lemmas before adding infrastructure.
- Added one immediately-used local helper lemma, `satisfiesTreeCondition_singleton_eq_of_childrenBag_eq`, to transport a tree condition across a bag-equivalent swap inside a unary parent.
- Reproved `satisfiesTreeCondition_order_five_via_mixed21` by swapping the inner `[2,1]` witness to `[1,2]`, transporting through the new helper, and invoking canonical `satisfiesTreeCondition_order_five_via_mixed12`.

## Result
- SUCCESS: the Aristotle bundle was rejected as incompatible/redundant for the current repo. Its `Legendre.lean` is a standalone scaffold that redefines `ButcherTableau`, `SatisfiesB`, and surrounding infrastructure, while current `main` already contains an in-repo proof of `ButcherTableau.gaussLegendreNodes_of_B_double`. No lemma was harvested.
- SUCCESS: `satisfiesTreeCondition_order_five_via_mixed12` remains canonical.
- SUCCESS: `satisfiesTreeCondition_order_five_via_mixed21` now routes through the canonical `...via_mixed12` theorem via bag transport instead of duplicating the direct computational proof.
- SUCCESS: one new helper lemma was added in `OpenMath/OrderConditions.lean`; no `RootedTree.lean` changes were needed.

## Dead ends
- Directly using `satisfiesTreeCondition_eq_of_childrenBag_eq` was insufficient because the mixed swap happens inside a unary wrapper, not at the top node.
- No compatible micro-lemma was available in the current API for that unary-wrapper transport, so a small local helper was necessary.

## Discovery
- The existing bag-facing API was already strong enough for the inner `[d₁, d₂] ~ [d₂, d₁]` swap via `BTree.node_childrenBag_eq_swap`.
- The only missing invariant for this refactor was a unary-parent transport step, which can be expressed locally without extending `RootedTree.lean`.
- The order-5 dispatcher still distinguishes the two witness orientations syntactically, but the swapped theorem is no longer a separate computational proof.

## Suggested next approach
- Continue the bag-first cleanup by targeting the next duplicated order-5 family where an inner permutation is still handled by parallel proof scripts rather than transport to a canonical orientation.
- If dispatcher cleanup becomes worthwhile, introduce a small canonical wrapper theorem for the mixed order-5 single-child case so both witness orientations rewrite through one entry point.

## Verification
- Ran `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderConditions.lean`
- Result: success, with only pre-existing linter warnings about unused `simp` arguments elsewhere in the file.
