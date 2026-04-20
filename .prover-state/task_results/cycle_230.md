# Cycle 230 Results

## Worked on
Removed the obsolete low-order ordered-list compatibility wrapper API from `OpenMath/RootedTree.lean`:
- `OrderThreeWitness`
- `order_three_witness_nonempty`
- `order_three_witness`
- `OrderFourWitness`
- `order_four_witness_nonempty`
- `order_four_witness`

Kept the bag-first low-order classifier boundary intact:
- `OrderThreeBagWitness`
- `order_three_bag_witness_nonempty`
- `order_three_bag_witness`
- `OrderFourBagWitness`
- `order_four_bag_witness_nonempty`
- `order_four_bag_witness`

## Approach
First re-checked the live tree for downstream consumers with:

```bash
rg -n "OrderThreeWitness|order_three_witness\\b|OrderFourWitness|order_four_witness\\b" OpenMath --glob '!OpenMath/RootedTree.lean'
```

This returned no hits, so the compatibility surface was dead outside `RootedTree.lean`.
I then deleted the order-3 and order-4 wrapper blocks from `OpenMath/RootedTree.lean` without changing the bag-first witness definitions, transport lemmas, or `OpenMath/OrderConditions.lean`.

The cycle strategy explicitly said not to poll or submit Aristotle unless new hard blockers appeared after real Lean progress. No blocker appeared, so no Aristotle jobs were submitted this cycle.

## Result
SUCCESS.

The order-3 and order-4 compatibility wrappers were removed entirely. The only live low-order classifier interface remains the bag-first witness boundary. `OpenMath/OrderConditions.lean` needed no changes.

## Dead ends
None in this cycle. The downstream search stayed empty, so there was no hidden consumer to migrate.

## Discovery
The remaining low-order ordered compatibility surface was genuinely dead: only `OpenMath/RootedTree.lean` still defined it, and removing it left `OrderConditions` compiling against the bag-first APIs exactly as intended.

The verification commands run were:

```bash
export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH
lake env lean OpenMath/RootedTree.lean
lake env lean OpenMath/OrderConditions.lean
lake build OpenMath.RootedTree
lake build OpenMath.OrderConditions
lake build
```

`OpenMath/OrderConditions.lean` still emits pre-existing linter warnings, but the targeted checks and builds succeed.

## Suggested next approach
Continue the rooted-tree representation cleanup by removing the next compatibility-only ordered fallback surface, keeping the bag-first API as the only public witness boundary for low-order tree classification.
