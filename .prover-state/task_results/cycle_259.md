# Cycle 259 Results

## Worked on
- Removed the public top-level order-5 compatibility wrapper `BTree.OrderFiveRecoveryWitness` together with `BTree.order_five_recovery_witness_nonempty` and `BTree.order_five_recovery_witness` from [OpenMath/RootedTree.lean](/mmfs1/gscratch/amath/mathai/OpenMath/OpenMath/RootedTree.lean).
- Rewired the reverse direction of `thm_301A_order5` in [OpenMath/OrderConditions.lean](/mmfs1/gscratch/amath/mathai/OpenMath/OpenMath/OrderConditions.lean) to dispatch directly on a top-level bag-first classification theorem.

## Approach
- Replaced the deleted wrapper with `BTree.order_five_node_classification`, a direct theorem for `(.node children).order = 5` that splits into:
  - 4-child all-leaf bushy5,
  - 3-child Case B with an `OrderFiveCaseBWitness`,
  - 2-child Case C with an `OrderFiveCaseCWitness`,
  - 1-child Case D with an `OrderFiveCaseDWitness`.
- Kept the existing bag-first Case B / Case C / Case D branch infrastructure unchanged and reused it immediately from the theorem-side reverse proof.
- Rewrote `thm_301A_order5` reverse direction to `rcases` on `order_five_node_classification` and then dispatch straight into the existing canonical branch theorems.
- Aristotle: no jobs were submitted this cycle. The planner state for cycle 259 explicitly said not to submit new Aristotle jobs unless this refactor created a genuinely hard new sublemma or a live `sorry`, and this refactor closed without introducing either.

## Result
- SUCCESS.
- `thm_301A_order5` now dispatches directly on top-level bag-first classification instead of `OrderFiveRecoveryWitness`.
- The old public order-5 wrapper was removed entirely rather than merely narrowed.
- Verification completed:
  - `lake env lean OpenMath/RootedTree.lean`
  - `lake env lean OpenMath/OrderConditions.lean`
  - `lake build`
  - `rg -n "OrderFiveRecoveryWitness|order_five_recovery_witness\\b" OpenMath`
- The final `rg` audit returned no matches.

## Dead ends
- The first version of `order_five_node_classification` tried to store witness values inside propositional conjunctions; Lean rejected that because `OrderFiveCaseB/C/DWitness` live in `Type`, not `Prop`. Repackaging those branches as existential witness packages fixed the issue cleanly.
- `lake env lean OpenMath/RootedTree.lean` typechecked the file but did not refresh the imported artifact that `OpenMath/OrderConditions.lean` was using, so I had to run `lake build OpenMath.RootedTree` once before rerunning the exact verification sequence.

## Discovery
- The remaining order-5 theorem boundary is now bag-first all the way through the top-level classifier.
- Residual general list-backed interface debt still remains in the broader rooted-tree API because the core datatype is still `BTree.node : List BTree → BTree`, and several recovery lemmas still convert bag equalities back into exact singleton/pair/triple/four-child list presentations when downstream proofs need literal node shapes.

## Suggested next approach
- Continue pushing the remaining general list-backed recovery surface downward, especially helper APIs that recover exact `List` presentations from bag equalities.
- Keep theorem boundaries bag-first and use exact-list recovery only as a local implementation detail where unavoidable.
