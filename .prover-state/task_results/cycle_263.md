# Cycle 263 Results

## Worked on
- `OpenMath/RootedTree.lean` public rooted-tree recovery API cleanup for arity 3 and 4.
- Added bag-first ternary/quaternary recovery witnesses:
  `BTree.ThreeChildRecoveryWitness`,
  `BTree.three_child_recovery_witness_of_childrenBag_eq`,
  `BTree.ThreeChildRecoveryWitness.canonicalBag_eq`,
  `BTree.FourChildRecoveryWitness`,
  `BTree.four_child_recovery_witness_of_childrenBag_eq`,
  `BTree.FourChildRecoveryWitness.canonicalBag_eq`.
- Demoted the old exact-list arity-3/4 helpers:
  `triple_children_exists_of_childrenBag_eq`,
  `four_children_exists_of_childrenBag_eq`,
  `triple_node_recover_of_childrenBag_eq`,
  `four_node_recover_of_childrenBag_eq`.

## Approach
- Followed the cycle strategy in `strategy.md` and worked only in `OpenMath/RootedTree.lean`.
- Used a local sorry-first pass to insert the new witness API and compatibility wrappers, verified the file shape with `lake env lean OpenMath/RootedTree.lean`, then discharged the sorries manually.
- Mirrored the existing unary/binary recovery API pattern:
  public witness structure + public constructor + public `canonicalBag_eq` transport lemma.
- Kept the old arity-3/4 exact-list helpers only as internal compatibility points by marking them `private`.
- Rewrote the old `triple_node_recover_of_childrenBag_eq` / `four_node_recover_of_childrenBag_eq` lemmas as thin wrappers over the new witness constructors.
- Audited the caller graph with `rg` before and after the change.

## Result
- SUCCESS.
- The new ternary/quaternary witness API was added in `OpenMath/RootedTree.lean`.
- `triple_children_exists_of_childrenBag_eq` and `four_children_exists_of_childrenBag_eq` were demoted to `private`.
- `triple_node_recover_of_childrenBag_eq` and `four_node_recover_of_childrenBag_eq` were demoted to `private` and now wrap the new witness constructors.
- No theorem-side consumers of arity-3/4 exact-list recovery remain. `rg` after the change showed no uses of those old names outside `OpenMath/RootedTree.lean`, and no `OrderConditions.lean` edits were needed.
- Verification passed:
  `lake env lean OpenMath/RootedTree.lean`
  `lake env lean OpenMath/OrderConditions.lean`
  `lake build`

## Dead ends
- The first ternary/quaternary constructor implementation tried to eliminate the `Prop`-valued existential witnesses from `triple_children_exists_of_childrenBag_eq` / `four_children_exists_of_childrenBag_eq` directly into the witness `Type`.
- Lean rejected that with the expected large-elimination restriction (`Exists.casesOn` only eliminating into `Prop`).
- Fixed by switching the constructors to direct list-length decomposition, exactly in the style of the existing binary recovery constructor.

## Discovery
- The old public arity-3/4 exact-list recovery surface was fully local to `OpenMath/RootedTree.lean`; there were no external consumers forcing those names to stay public.
- The theorem-side public consumers in `OpenMath/OrderConditions.lean` remain only on the unary/binary bag-first APIs.
- After this cycle, the public arity-specific bag-first recovery surface in `RootedTree.lean` is now:
  `OneChildRecoveryWitness`,
  `one_child_recovery_witness_of_childrenBag_eq`,
  `TwoChildRecoveryWitness`,
  `two_child_recovery_witness_of_childrenBag_eq`,
  `ThreeChildRecoveryWitness`,
  `three_child_recovery_witness_of_childrenBag_eq`,
  `FourChildRecoveryWitness`,
  `four_child_recovery_witness_of_childrenBag_eq`,
  together with the binary/ternary/quaternary `canonicalBag_eq` transport lemmas.
- Aristotle was not used this cycle. The strategy explicitly said not to submit new jobs unless a genuinely new hard focused lemma appeared after a local sorry-first skeleton. This cycle stayed within mechanical rooted-tree API cleanup and did not produce such a lemma.

## Suggested next approach
- Audit whether any remaining public rooted-tree recovery names still expose ordered child-list data more than necessary, especially outside the arity-1/4 bag-first witness layer.
- If theorem-side ternary/quaternary consumers appear in later cycles, consume the new `ThreeChildRecoveryWitness` / `FourChildRecoveryWitness` APIs directly and keep bag equality as the transport boundary.
