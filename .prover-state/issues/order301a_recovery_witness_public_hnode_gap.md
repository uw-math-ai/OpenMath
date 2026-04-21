# Issue: Order 301A Recovery Witness Public hnode Gap

## Blocker
After cycle 265, the arity-3/4 exact-list compatibility wrappers are gone and the 3-child/4-child witness structures no longer expose `hnode`. The remaining public exact-list leak is the one-/two-child recovery witness path:

- `OneChildRecoveryWitness.hnode` at `OpenMath/RootedTree.lean:977`
- `TwoChildRecoveryWitness.hnode` at `OpenMath/RootedTree.lean:1024`

These fields are still used by the local transport lemmas:

- `OneChildRecoveryWitness.binary_right_eq` at line 992
- `OneChildRecoveryWitness.nestedSingleton_eq` at line 999
- `TwoChildRecoveryWitness.binary_right_eq` at line 1039
- `TwoChildRecoveryWitness.nestedSingleton_eq` at line 1047

Removing those public `hnode` fields is no longer a local wrapper deletion. It requires reworking the transport API that theorem code uses to move from recovered child data back to exact outer-node equalities.

## Context
The current one-/two-child theorem-facing transport lemmas are implemented by rewriting with `hw.hnode`. That means the exact list presentation is still part of the public witness representation, even though theorem code usually consumes the transport lemmas rather than calling `.hnode` directly.

Cycle 265 showed that the arity-3/4 cleanup was local because their `hnode` fields had no surviving consumers. The one-/two-child case is different: the public fields are coupled to named transport lemmas that encode exact-node rewrites.

## What was tried
- Audited all arity-3/4 witness and wrapper usage in `OpenMath/RootedTree.lean` and `OpenMath/OrderConditions.lean`.
- Deleted the dead private wrappers:
  - `triple_node_recover_of_childrenBag_eq`
  - `four_node_recover_of_childrenBag_eq`
- Removed the now-unused public `hnode` fields from:
  - `ThreeChildRecoveryWitness`
  - `FourChildRecoveryWitness`

I did not remove `OneChildRecoveryWitness.hnode` or `TwoChildRecoveryWitness.hnode` in the same cycle, because that would have required redesigning the transport lemmas that currently expose exact outer-node equalities to theorem code.

## Possible solutions
- Introduce an internal transport layer for one-/two-child recovery witnesses so the public structure carries only bag-facing data and theorem code calls dedicated transport lemmas that do not expose the underlying exact witness representation.
- Replace the current `binary_right_eq` and `nestedSingleton_eq` lemmas with bag-first equivalence lemmas and migrate theorem consumers to use children-bag transport plus node invariance lemmas instead of direct rewriting.
- If exact outer-node equalities are still required, package them in private/internal helper lemmas rather than public structure fields, then update the theorem boundary to depend only on those lemmas.
