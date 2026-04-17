# Cycle 099 Results

## Worked on
Theorem 301A infrastructure in `OpenMath/RootedTree.lean`:
- new `BTree` type for rooted trees
- recursive definitions of `order`, `symmetry`, `density`
- derived counts `alpha` and `beta`
- small-tree regression examples through order `4`

## Approach
Started from the planner's intended multiset model, then tested it in Lean. The kernel rejects
`inductive BTree | node : Multiset BTree → BTree` as an invalid recursive occurrence, so I
switched to the approved `List BTree` fallback.

For the list model:
- `order` and `density` are defined by recursion over the child list using `foldr`
- `symmetry` is defined with an auxiliary right-to-left scan `symmetryScan` that only contributes
  a multiplicity factor at the final occurrence of each subtree class
- Theorem 301A base cases and recursive equations were stated and proved in the list-based form
- Added computed examples for the order-2, order-3, and order-4 trees

I also checked the old Aristotle artifact `54cb7170...` first. It is the redundant
Picard-Lindelöf result noted by the planner, so I did not modify the codebase with it.

## Result
SUCCESS.

`OpenMath/RootedTree.lean` now compiles with:

```bash
export PATH="/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH"
export LEAN_CC=/usr/bin/gcc
export LIBRARY_PATH="/tmp/lean4-toolchain/lib:/tmp/lean4-toolchain/lib/lean"
lake env lean OpenMath/RootedTree.lean
```

Tracking updates completed:
- `plan.md` marks Theorem 301A as in progress
- `extraction/formalization_data/lean_status.json` marks `thm:301A` as `in_progress`

## Dead ends
- The intended multiset definition failed at the kernel level:
  `arg #1 of 'BTree.node' contains a non valid occurrence of the datatypes being declared`
- I did not push further on the multiset approach after confirming the fallback was necessary.

## Discovery
- Direct recursion through `List.foldr` is accepted for `order` and `density` once the
  `sizeOf` obligations are discharged with `List.sizeOf_lt_of_mem`.
- The list fallback is good enough to start Chapter 3 tree infrastructure, but it still treats
  sibling order as data. Any later theorem that genuinely needs unordered multiplicities should
  either canonicalize child order or replace the representation.
- Aristotle successfully checked the new file in project
  `f55adb39-efd2-49fc-a4a1-231e49029c98` and suggested extra order-4 examples; I incorporated
  the added test coverage and kept the explicit local termination proofs.

## Suggested next approach
- Replace the `List` fallback with a genuinely unordered representation if later tree theorems
  need quotient-free permutation invariance.
- Otherwise proceed to Theorem 302A using the current `BTree` API, then revisit representation
  details only if they become a proof bottleneck.
