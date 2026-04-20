# Cycle 212 Results

## Worked on
Order-5 rooted-tree canonicalization cleanup in `OpenMath/OrderConditions.lean`, starting with the `{1, bushy-3}` family and then the `{1, chain-3}` family.

## Approach
Read the live canonical transport boundary first:
- `satisfiesTreeCondition_order_five_bushy3_eq_of_childrenBag_eq`
- `satisfiesTreeCondition_order_five_bushy3_canonical`
- `satisfiesTreeCondition_order_five_chain3_eq_of_childrenBag_eq`
- `satisfiesTreeCondition_order_five_chain3_canonical`
- `satisfiesTreeCondition_order_five_via_mixed_eq_of_childrenBag_eq`
- `satisfiesTreeCondition_order_five_via_mixed_canonical`
- `order_five_caseD_dispatch_shared`
- `satisfiesTreeCondition_order_five_caseD`
- the `thm_301A_order5` branches that still referenced ordered wrappers

Then changed the forward `thm_301A_order5` extraction branches for `t5c` and `t5d` to use the canonical bag-based family lemmas directly instead of the orientation-specific `[1, bushy-3]` / `[1, chain-3]` entry points. After that, deleted the now-dead reverse wrapper stack for bushy-3 and the reverse tree-condition wrapper for chain-3.

There were no ready Aristotle results to incorporate this cycle, per the planner’s triage. I did not do blind Aristotle polling. I also did not submit new Aristotle jobs, because this cycle’s work was a local theorem-boundary refactor with no new `sorry`-structured proof obligations to batch out.

## Result
SUCCESS.

The following reverse-orientation wrappers were removed or bypassed as independent boundaries:
- removed `ew_of_order_five_bushy3_1`
- removed `density_of_order_five_bushy3_1`
- removed `satisfiesTreeCondition_order_five_bushy3_1`
- removed `satisfiesTreeCondition_order_five_chain3_1`
- bypassed the old ordered entry points in the forward `thm_301A_order5` branches for `t5c` and `t5d` by routing through `..._canonical`

No `RootedTree.lean` helper was added. Existing `childrenBag` transport lemmas were sufficient.

## Dead ends
Initial direct `rw` against `t5c` / `t5d` failed because the goal still mentioned the named tree constants rather than their `BTree.node [...]` definitions. This was fixed with explicit `change` steps before rewriting by the canonical lemmas.

## Discovery
The reverse side of the order-5 dispatcher was already using canonical witnesses. The remaining theorem-level dependency on ordered wrappers was in the forward half of `thm_301A_order5`, specifically the `order5d` and `order5f` extraction branches.

## Suggested next approach
Continue with the unary mixed `{1,2}` family and remove the remaining reverse-orientation wrapper boundary there:
- `ew_of_order_five_via_mixed21`
- `satisfiesTreeCondition_order_five_via_mixed21`

The next cleanup should mirror this cycle: route any remaining theorem-level callers through `satisfiesTreeCondition_order_five_via_mixed_canonical`, then delete dead reverse wrappers if no consumers remain.

## Verification
Commands run:

```bash
export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH
lake env lean OpenMath/OrderConditions.lean
```

Result:
- `OpenMath/OrderConditions.lean` compiled successfully
- only pre-existing warnings remained (unused `simp` args / `ring_nf` suggestions)
