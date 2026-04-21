# Cycle 265 Results

## Worked on
`OpenMath/RootedTree.lean` arity-3/4 rooted-tree recovery witness cleanup for the Theorem 301A infrastructure upgrade.

## Approach
- Audited the live arity-3/4 surface in `OpenMath/RootedTree.lean` and `OpenMath/OrderConditions.lean`.
- Confirmed `triple_node_recover_of_childrenBag_eq` and `four_node_recover_of_childrenBag_eq` were unused.
- Removed those dead private exact-list compatibility wrappers.
- Shrunk the public arity-3 and arity-4 witness structures to bag-facing data only by deleting their `hnode` fields.
- Recompiled `OpenMath/RootedTree.lean`, then `OpenMath/OrderConditions.lean`, then ran `lake build`.
- Per the cycle strategy, did not submit Aristotle jobs: this cycle had no live sorrys and was explicitly designated as local infrastructure cleanup rather than a sorry-closing cycle.

## Result
SUCCESS

- `triple_node_recover_of_childrenBag_eq` was deleted.
- `four_node_recover_of_childrenBag_eq` was deleted.
- No new arity-3/4 transport wrapper was added.
- `ThreeChildRecoveryWitness` and `FourChildRecoveryWitness` no longer expose public `hnode` fields.
- Verification passed:
  - `lake env lean OpenMath/RootedTree.lean`
  - `lake env lean OpenMath/OrderConditions.lean`
  - `lake build`

## Dead ends
- I considered leaving the arity-3/4 public `hnode` fields in place and only deleting the dead wrappers, but there were no surviving consumers of those fields, so keeping them would have left avoidable exact-list leakage in the public witness API.

## Discovery
- After the cleanup, the only remaining recovery-witness `hnode` surface is the one-/two-child path in `OpenMath/RootedTree.lean`:
  - public fields: lines 977 and 1024
  - local transport lemmas using `.hnode`: lines 992, 999, 1039, 1047
- The arity-3/4 witness API is now bag-first only.
- The remaining other `hnode` names in `RootedTree.lean` and `OrderConditions.lean` are local termination proofs (`have hnode := ...`), not witness-surface exact-list leakage.

## Suggested next approach
- If the Theorem 301A cleanup needs to continue shrinking public exact-list witnesses, migrate the one-/two-child transport path away from public `hnode` fields by introducing a more internal transport representation and updating downstream theorem helpers to consume it.
- The blocker for that broader change is recorded in `.prover-state/issues/order301a_recovery_witness_public_hnode_gap.md`.
