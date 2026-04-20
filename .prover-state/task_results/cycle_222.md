# Cycle 222 Results

## Worked on
- `OpenMath/RootedTree.lean`
- `OpenMath/OrderConditions.lean`
- theorem 301A order-3 and order-4 witness plumbing

## Approach
- Added a bag-first low-order witness layer:
  `OrderThreeBagWitness`, `order_three_bag_witness_nonempty`,
  `order_three_bag_witness`, `OrderFourBagWitness`,
  `order_four_bag_witness_nonempty`, and `order_four_bag_witness`.
- Kept the older ordered witnesses in place as compatibility API.
- Rewired `thm_301A_order3` and `thm_301A_order4` to case-split on the new
  bag witnesses and transport into the existing canonical ordered theorems via
  `childrenBag` equalities.
- Moved the singleton-child bag-transport helper earlier in
  `OpenMath/OrderConditions.lean` so the order-4 singleton branch can consume
  a bag witness for its order-3 child.

## Result
- SUCCESS
- `thm_301A_order3` now depends on `OrderThreeBagWitness` instead of the older
  ordered witness API.
- `thm_301A_order4` now depends on `OrderFourBagWitness`; its singleton-child
  branch transports through the new bag witness for the order-3 child.
- Verified with:
  `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/RootedTree.lean`
- Verified with:
  `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderConditions.lean`
- Also rebuilt module artifacts with:
  `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build OpenMath.RootedTree OpenMath.OrderConditions`

## Dead ends
- `OrderConditions.lean` initially could not see the new witness declarations
  after a direct `lake env lean` run because the imported `.olean` for
  `OpenMath.RootedTree` was stale. Rebuilding the affected modules fixed that.
- The first attempt at moving
  `satisfiesTreeCondition_singleton_eq_of_childrenBag_eq` produced the wrong
  `convert` shape; restoring the previous successful proof structure fixed it.

## Discovery
- The minimal useful bag-first payload for this cycle is:
  an arbitrary child list plus a `childrenBag` equality to a canonical ordered
  representative. That is enough to move theorem consumers off ordered-list
  plumbing without rewriting the canonical order-condition lemmas.
- The order-4 singleton branch benefits from a dedicated unary-parent transport
  lemma; otherwise nested bag witnesses force the caller back into ordered
  equalities.

## Suggested next approach
- Rework `order_five_caseC_witness_nonempty` and
  `order_five_caseD_witness_nonempty` onto bag-first subwitnesses so the
  remaining order-5 callers stop depending on `OrderThreeWitness` and
  `OrderFourWitness`.
- If that starts to duplicate transport logic, introduce a small shared
  bag-to-canonical dispatcher helper instead of new family-specific theorem
  variants.

## Aristotle
- No Aristotle batch was submitted this cycle.
- Reason: the cycle strategy explicitly forbade submitting a new batch unless
  the refactor first created a genuinely new hard subgoal. This cycle stayed
  within a controlled witness/API migration and closed without new unresolved
  hard proof obligations.
