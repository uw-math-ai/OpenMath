# Cycle 264 Results

## Worked on
- Public-surface cleanup for rooted-tree recovery witnesses in `OpenMath/RootedTree.lean`.
- The four theorem-side `.hnode` call sites in `OpenMath/OrderConditions.lean`:
  - `satisfiesTreeCondition_order_five_1_bushy3`
  - `satisfiesTreeCondition_order_five_1_chain3`
  - `satisfiesTreeCondition_order_five_via_via_bushy3_canonical`
  - `satisfiesTreeCondition_order_five_via_via_chain3_canonical`

## Approach
- Added thin wrapper lemmas around the existing one-child and two-child recovery witnesses so theorem code can transport through recovered exact nodes without directly rewriting by the witness field `.hnode`.
- Reworked the two binary-parent order-5 lemmas to rewrite the outer node via the new recovery wrapper first, then reuse the existing exact proof bodies.
- Reworked the two nested-unary canonical lemmas to combine:
  - `satisfiesTreeCondition_singleton_eq_of_tree_childrenBag_eq`
  - the new nested recovery transport wrappers
  - existing canonical bag-equality transport on the reconstructed inner node
- Rebuilt `OpenMath.RootedTree` before recompiling `OpenMath/OrderConditions.lean` so the downstream file saw the new recovery-wrapper declarations.
- Aristotle was not used this cycle. The cycle strategy explicitly said not to use Aristotle preemptively, and this cleanup did not introduce any new hard lemma or sorry-first proof skeleton that needed batch submission.

## Result
- SUCCESS.
- Added these wrapper lemmas in `OpenMath/RootedTree.lean`:
  - `BTree.OneChildRecoveryWitness.canonicalBag_eq`
  - `BTree.OneChildRecoveryWitness.binary_right_eq`
  - `BTree.OneChildRecoveryWitness.nestedSingleton_eq`
  - `BTree.TwoChildRecoveryWitness.binary_right_eq`
  - `BTree.TwoChildRecoveryWitness.nestedSingleton_eq`
- Removed the four targeted theorem-side `.hnode` uses from `OpenMath/OrderConditions.lean`.
- After the refactor, `rg -n '\.hnode' OpenMath/RootedTree.lean OpenMath/OrderConditions.lean` shows no `.hnode` uses in `OrderConditions.lean`.
- Remaining `.hnode` dependence is internal to `RootedTree.lean`:
  - inside the new wrapper lemmas themselves
  - inside the existing private three-/four-child compatibility wrappers
- No unavoidable theorem-side dependence on `.hnode` remains at the targeted order-5 call sites.

## Dead ends
- Attempted to rewrite the two early order-5 lemmas through later-in-file helper theorems (`..._bushy3_eq_of_childrenBag_eq` / `..._chain3_eq_of_childrenBag_eq`), but those helpers are defined after the target lemmas, so Lean rejected the forward references.
- Switched those two lemmas back to their local exact proof bodies after the wrapper-based rewrite step.

## Discovery
- The new wrapper lemmas live in the imported environment as expected, but `lake env lean OpenMath/OrderConditions.lean` needed an updated `OpenMath.RootedTree.olean`; just checking `OpenMath/RootedTree.lean` was not enough for downstream imports.
- For this cleanup, bag transport was sufficient once the exact-rewrite step was hidden behind witness wrapper lemmas.

## Suggested next approach
- Continue replacing remaining public theorem-side exact-node transports with named recovery wrappers so `OrderConditions.lean` stays on the bag-first interface.
- If later order-5 canonical lemmas still need repeated exact rewrites under fixed outer contexts, factor those contexts into additional narrow witness transport lemmas rather than reopening `.hnode` in theorem code.
