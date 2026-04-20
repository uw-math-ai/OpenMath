# Cycle 244 Results

## Worked on
Theorem 301A order-5 singleton-child Case D representation boundary in `OpenMath/OrderConditions.lean`, specifically:
- `satisfiesTreeCondition_order_five_via_bushy4`
- `satisfiesTreeCondition_order_five_via_mixed12`
- `satisfiesTreeCondition_order_five_via_mixed_canonical`
- `order_five_caseD_dispatch_shared`

## Approach
Audited the live Case D boundary in `RootedTree.lean` and `OrderConditions.lean` first.

The rooted-tree witness layer was already bag-first, so the remaining debt was in theorem interfaces and the immediate dispatcher path. I:
- split the old exact-list proofs into internal `_exact` helper lemmas,
- replaced the public first-level Case D family boundaries with bag-first statements,
- added one local singleton transport helper for children with equal `childrenBag`,
- rewired the mixed canonical theorem and the Case D dispatcher to consume bag-first data directly instead of reconstructing exact child lists locally.

## Result
SUCCESS.

Visible Lean progress:
- `satisfiesTreeCondition_order_five_via_bushy4` now takes bag-first data
  `c.childrenBag = (BTree.node [d₁, d₂, d₃]).childrenBag`
  together with order facts, rather than an existential exact-list presentation.
- `satisfiesTreeCondition_order_five_via_mixed12` now takes bag-first data
  `c.childrenBag = (BTree.node [d₁, d₂]).childrenBag`
  together with `d₁.order = 1` and `d₂.order = 2`.
- `satisfiesTreeCondition_order_five_via_mixed_canonical` no longer reconstructs literal child lists before dispatching.
- `order_five_caseD_dispatch_shared` now dispatches directly from the bag-first `OrderFiveCaseDWitness` branches, without theorem-local exact-list recovery in the first-level `bushy4` and `mixed4` cases.

## Dead ends
Directly replacing the theorem statements in place caused self-reference in the proof bodies. The fix was to preserve the existing exact-list proofs as internal `_exact` lemmas and make the bag-first theorems thin transport wrappers over them.

## Discovery
No new `RootedTree.lean` API was needed. The only missing piece was a local unary transport lemma in `OrderConditions.lean` for arbitrary trees `c d` with `c.childrenBag = d.childrenBag`.

The pre-existing `OrderFiveCaseDWitness` interface was already the correct bag-first abstraction; the remaining representation debt was entirely in the order-condition theorem boundary and its consumer path.

## Suggested next approach
Continue the same cleanup pattern for any remaining exact-list theorem boundaries in the order-5 rooted-tree pipeline, but keep the scope local to the immediate consumer path each time. The current first-level singleton-child Case D boundary is now bag-first end-to-end.
