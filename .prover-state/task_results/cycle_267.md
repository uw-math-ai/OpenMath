# Cycle 267 Results

## Worked on
Theorem 301A rooted-tree infrastructure cleanup, specifically the remaining public arity-3/4 recovery surface in `OpenMath/RootedTree.lean`:

- `ThreeChildRecoveryWitness`
- `ThreeChildRecoveryWitness.canonicalBag_eq`
- `three_child_recovery_witness_of_childrenBag_eq`
- `FourChildRecoveryWitness`
- `FourChildRecoveryWitness.canonicalBag_eq`
- `four_child_recovery_witness_of_childrenBag_eq`

## Approach
- Read `.prover-state/strategy.md` and followed the cycle-267 plan.
- Audited the live tree with:
  - `rg -n '\.hnode' OpenMath/RootedTree.lean OpenMath/OrderConditions.lean`
  - `rg -n 'ThreeChildRecoveryWitness|FourChildRecoveryWitness|three_child_recovery_witness_of_childrenBag_eq|four_child_recovery_witness_of_childrenBag_eq' OpenMath .prover-state --glob '!**/aristotle_results/**' --glob '!**/.lake/**'`
- Confirmed that `OpenMath/OrderConditions.lean` has no `.hnode` uses and that the 3-/4-child recovery API had no `OpenMath/` consumers outside its own definitions.
- Deleted that dead public arity-3/4 recovery surface from `OpenMath/RootedTree.lean` instead of merely marking it `private`, because it had no remaining in-repo use.
- Re-checked the live surface and then ran the required verification commands.

## Result
SUCCESS

- Removed the unused public 3-/4-child recovery witness API from `OpenMath/RootedTree.lean`.
- The remaining `.hnode` theorems in `OpenMath/RootedTree.lean` are private one-/two-child internals only.
- `OpenMath/OrderConditions.lean` still has no `.hnode` consumers.
- No `OpenMath/` references to the deleted 3-/4-child API remain.
- Verification passed:
  - `lake env lean OpenMath/RootedTree.lean`
  - `lake env lean OpenMath/OrderConditions.lean`
  - `lake build`

## Dead ends
- None in Lean proof search. This cycle was a representation-surface audit and deletion cleanup, not a new proof decomposition.
- I did not use Aristotle. The cycle strategy explicitly said not to poll or submit Aristotle jobs because there were no pending results and no active `sorry`s, and this cleanup introduced no new `sorry`s.

## Discovery
- The apparent remaining arity-3/4 bag-first witness API was fully dead: after the audit, its only live mentions were the definitions themselves plus historical `.prover-state` notes.
- The one-/two-child recovery boundary is now bag-first from the theorem side: the exact node equalities exist only as `private` internals inside `OpenMath/RootedTree.lean`, with public transport lemmas used instead.

## Suggested next approach
- Pivot away from rooted-tree representation cleanup unless a new theorem-side consumer reveals a real leak.
- If Theorem 301A work continues in this area, focus only on a concrete downstream theorem dependency, not on further speculative recovery-API pruning.
