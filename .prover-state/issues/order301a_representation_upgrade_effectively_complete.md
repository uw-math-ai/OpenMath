# Issue: Order 301A representation upgrade effectively complete

## Blocker
There is no longer a live theorem-facing rooted-tree representation leak to clean up in the current source tree.

## Context
- Audit command:
  - `rg -n '\.hnode' OpenMath/RootedTree.lean OpenMath/OrderConditions.lean`
- Result:
  - `.hnode` appears only in `OpenMath/RootedTree.lean`
  - `OpenMath/OrderConditions.lean` has no `.hnode` consumers
- Audit command:
  - `rg -n 'ThreeChildRecoveryWitness|FourChildRecoveryWitness|three_child_recovery_witness_of_childrenBag_eq|four_child_recovery_witness_of_childrenBag_eq' OpenMath .prover-state --glob '!**/aristotle_results/**' --glob '!**/.lake/**'`
- Result before edit:
  - the only `OpenMath/` hits were the definitions inside `OpenMath/RootedTree.lean`
- Action taken in cycle 267:
  - deleted the dead public arity-3/4 recovery API from `OpenMath/RootedTree.lean`
- Result after edit:
  - no `OpenMath/` references to that arity-3/4 surface remain
  - the remaining `OneChildRecoveryWitness.hnode` and `TwoChildRecoveryWitness.hnode` are `private` theorems internal to `OpenMath/RootedTree.lean`
  - theorem-facing code uses the bag transport lemmas instead

## What was tried
- Verified the live source tree before editing.
- Removed the unused public 3-/4-child recovery surface entirely rather than just demoting it to `private`.
- Rebuilt:
  - `lake env lean OpenMath/RootedTree.lean`
  - `lake env lean OpenMath/OrderConditions.lean`
  - `lake build`

## Possible solutions
- Planner should pivot away from rooted-tree representation cleanup next cycle.
- Reopen this area only if a specific downstream theorem exposes a concrete list-sensitive or exact-node-equality dependency in public theorem code.
