# Cycle 197 Results

## Worked on
Forward-direction singleton-child order-5 cases in `OpenMath/OrderConditions.lean` inside `thm_301A_order5`, specifically:
- `order5e` from `t5f = [t4a]`
- `order5g` from `t5g = [t4b]`
- `order5h` from `t5h = [t4c]`
- `order5i` from `t5i = [t4d]`

## Approach
Added one local helper package `extract_caseD_forward` in the forward branch of `thm_301A_order5`. It groups four witness-shaped extraction functions for the order-5 singleton-child Case D family:
- bushy4 to `tab.order5e`
- mixed4 to `tab.order5g`
- viaBushy3 to `tab.order5h`
- viaChain3 to `tab.order5i`

Each component rewrites `tab.satisfiesTreeCondition (.node [c])` through the existing normalized Case D infrastructure and then finishes with the corresponding `order5*_sum_eq` lemma. The concrete `t5f/t5g/t5h/t5i` branches now call the packaged helper instead of repeating separate inline `rw` scripts.

## Result
SUCCESS. The forward singleton-child family was refactored to remove the four duplicated explicit tree-shape rewrite blocks. No new file-level infrastructure outside `OpenMath/OrderConditions.lean` was needed.

## Dead ends
An initial dependent helper indexed directly by `OrderFiveCaseDWitness` failed because the witness lives in `Prop`, so eliminating it into a dependent nontrivial match motive caused a `propRecLargeElim` error. Replaced that with a non-dependent conjunction package of four extraction functions.

## Discovery
The right normalization boundary on the forward side is still the existing low-level rewrite lemmas:
- `satisfiesTreeCondition_order_five_via_bushy4`
- `satisfiesTreeCondition_order_five_via_mixed_canonical`
- `satisfiesTreeCondition_order_five_via_via_bushy3`
- `satisfiesTreeCondition_order_five_via_via_chain3`

Packaging those four rewrites behind one local conjunction is enough to remove the duplicated forward singleton-child extraction code without touching `RootedTree.lean` or broadening the witness API.

## Suggested next approach
If more cleanup is needed in this theorem neighborhood, the next small step is to see whether the forward and reverse Case D local dispatchers can share an even tighter local packaging theorem without introducing dependent elimination on `OrderFiveCaseDWitness`.

## Aristotle
No Aristotle submission this cycle. There were no ready results to harvest at cycle start, and this refactor was completed without introducing fresh focused `sorry`s.

## Verification
Ran:

```bash
export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH
lake env lean OpenMath/OrderConditions.lean
```
