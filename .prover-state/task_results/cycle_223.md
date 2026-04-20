# Cycle 223 Results

## Worked on
- `OpenMath/OrderConditions.lean`
- `order_five_caseC_witness_nonempty`
- `order_five_caseD_witness_nonempty`

## Approach
- Added three tiny private transport helpers near the order-5 Case C witness layer:
  `singleton_children_eq_of_childrenBag_eq`,
  `pair_children_exists_of_childrenBag_eq`,
  `triple_children_exists_of_childrenBag_eq`.
- Refactored `order_five_caseC_witness_nonempty` to consume
  `BTree.OrderThreeBagWitness` / `BTree.order_three_bag_witness`.
- In the chain-3 branch, used singleton bag equality to recover the exact
  canonical unary child.
- In the bushy-3 branch, recovered the actual ordered child list from the bag
  equality and derived the order-1 facts locally from the order sum.
- Refactored `order_five_caseD_witness_nonempty` to consume
  `BTree.OrderFourBagWitness` / `BTree.order_four_bag_witness`.
- For `bushy4` and `mixed4`, recovered the actual child list shape from the bag
  equality and derived the needed order facts locally.
- For the `single3` branch, kept the bag-first payload all the way down to the
  nested order-3 witness and only used singleton transport where exact unary
  equality was required by the existing witness constructor.

## Result
- SUCCESS.
- `order_five_caseC_witness_nonempty` no longer uses
  `BTree.OrderThreeWitness` / `BTree.order_three_witness`.
- `order_five_caseD_witness_nonempty` no longer uses
  `BTree.OrderFourWitness` / `BTree.order_four_witness`, and its nested order-3
  branch stays bag-first as well.
- `OpenMath/OrderConditions.lean` now has no remaining active uses of
  `OrderThreeWitness`, `OrderFourWitness`, `order_three_witness`, or
  `order_four_witness`.
- Verification completed:
  - `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/RootedTree.lean`
  - `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderConditions.lean`

## Dead ends
- Directly reusing the canonical children stored inside the bag witnesses was
  not sufficient, because the existing `OrderFiveCaseCWitness` and
  `OrderFiveCaseDWitness` constructors still require exact equalities of the
  fallback ordered child lists.
- The clean way through was to recover only the actual list shape from bag
  equality and then re-derive the required order facts locally.

## Discovery
- For this witness layer, singleton bag transport needs exact list recovery,
  while pair/triple cases only need list-shape recovery plus local order-sum
  arguments.
- That keeps the refactor narrow and avoids changing the existing order-5
  witness types or dispatch theorems.
- Aristotle was not used this cycle. The planner explicitly forbade polling at
  the start and forbade a new batch unless the cycle created a genuinely new
  hard subgoal beyond witness plumbing; this refactor stayed local and did not
  create such a subgoal.

## Suggested next approach
- Continue checking whether any remaining active theorem-construction code still
  depends on ordered-list witness compatibility wrappers outside these two
  witness constructors.
- If the planner still wants wrapper cleanup, make it a follow-up pass only if
  it stays local and does not disturb the now-green order-5 dispatcher path.
