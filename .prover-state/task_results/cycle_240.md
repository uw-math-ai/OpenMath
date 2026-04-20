# Cycle 240 Results

## Worked on
`BTree.OrderFiveCaseDWitness` in `OpenMath/RootedTree.lean` and the Case D consumer path in `OpenMath/OrderConditions.lean` for `thm_301A_order5`.

## Approach
Refactored the Case D rooted-tree witness away from exact ordered-node equalities and toward bag-first payloads:
- `bushy4` now stores `c.childrenBag = (node [d₁,d₂,d₃]).childrenBag`.
- `mixed4` now stores `c.childrenBag = (node [d₁,d₂]).childrenBag`.
- `viaChain3` and `viaBushy3` now store singleton/pair `childrenBag` equalities instead of exact nested node equalities.

Then updated the theorem-side canonical wrappers and dispatcher in `OrderConditions.lean` so ordered children are recovered only locally from the bag equalities using the public rooted-tree recovery lemmas and bag-invariance lemmas.

## Result
SUCCESS.

Visible Lean-code progress landed on the live Case D boundary:
- `OrderFiveCaseDWitness` stores less exact ordered-list equality data than before.
- `order_five_caseD_target`, `order_five_caseD_dispatch_shared`, and the forward/reverse Case D branches of `thm_301A_order5` now consume the new bag-first witness shape.

## Dead ends
- A first pass tried to keep theorem-side wrappers too close to the old exact-equality proofs. That ran into dependent-elimination friction when pattern matching on indexed witnesses.
- The working fix was to recover ordered singleton/pair/triple presentations only inside the local canonical lemmas and dispatch branches, instead of trying to preserve old equalities through the witness API.

## Discovery
- After case-splitting on indexed Case D witnesses, Lean often normalizes `childrenBag` equalities enough that branch-local proofs can reuse either `Multiset.card` contradictions or exact node equalities derived from the recovered child list.
- The bag-first witness boundary is now consistent with the earlier Case B/Case C direction: public witness payloads stay unordered, while theorem-side canonical lemmas perform any ordered recovery they need.

## Suggested next approach
Continue the Theorem 301A representation cleanup by looking for the next remaining theorem-side branch that still exports exact ordered child equalities instead of bag-first data. If the next boundary is another indexed witness family, prefer the pattern used here: store `childrenBag` equalities in the witness and recover ordered fallback children only inside the canonical theorem wrappers.

## Aristotle
No Aristotle incorporation or fresh Aristotle submission this cycle. The planner explicitly reported that there were no completed Aristotle results ready for incorporation and instructed not to start a fresh batch.

## Verification
Ran:
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/RootedTree.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderConditions.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build OpenMath.RootedTree OpenMath.OrderConditions`
