# Cycle 198 Results

## Worked on
`OpenMath/OrderConditions.lean`, specifically the order-5 / Case D cleanup inside `thm_301A_order5`.

## Approach
Removed the local forward-only `extract_caseD_forward` helper and introduced a shared Case D normalization boundary:
- `order_five_caseD_target`
- `order_five_caseD_dispatch_shared`

To support shared branch dispatch, I also changed the private `OrderFiveCaseDWitness` packaging from `Prop` to a private inductive data witness, proved `order_five_caseD_witness_nonempty`, and defined `order_five_caseD_witness` via `Classical.choice`.

## Result
SUCCESS.

The forward singleton-child call sites for `t5f`, `t5g`, `t5h`, and `t5i` now all use `order_five_caseD_dispatch_shared` to extract `order5e/g/h/i`.

The reverse Case D branch driven by `hD` now also uses the same shared dispatcher:
- it constructs `hCaseD : OrderFiveCaseDWitness c`
- packages the matching branch target as `order_five_caseD_target tab hCaseD`
- feeds that into `(order_five_caseD_dispatch_shared tab hrc hCaseD).2`

This removed the old duplicated local `extract_caseD_forward` proof block and the duplicated reverse-side conversion block for `h5e' / h5g' / h5h' / h5i'`.

## Dead ends
Tried first to keep the shared target packaging local to `thm_301A_order5` while indexing it directly by the original `Prop`-valued witness. Lean rejected that with `propRecLargeElim`, because the dispatcher needed to compute branch-specific targets from a proof-irrelevant witness.

## Discovery
The real mismatch between the forward and reverse Case D consumers was not the witness constructors themselves, but the fact that the shared branch target had to be computed from the witness. Making the private witness a data type instead of a proposition resolved that cleanly without changing any public theorem statement.

`order_five_caseD_dispatch_shared` needs `hrc` so that each branch can normalize through `order5e_sum_eq`, `order5g_sum_eq`, `order5h_sum_eq`, and `order5i_sum_eq`.

## Suggested next approach
Continue reducing local order-5 duplication by checking whether the remaining Case C / Case D reverse wrappers can share a similarly small target-packaging boundary, but keep the work inside `OpenMath/OrderConditions.lean`.

## Aristotle
No Aristotle jobs were submitted this cycle. The planner strategy for cycle 198 explicitly said there were no ready results to incorporate and to avoid new submissions unless fresh focused `sorry`s were introduced. This refactor completed without introducing any `sorry`.

## Verification
Ran:

```bash
export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH
lake env lean OpenMath/OrderConditions.lean
```
