# Cycle 571 Results

## Worked on
`OpenMath/OrderConditions.lean` elementary-weight list helpers and
`OpenMath/ButcherGroup/Section386Conv.lean` §386 general convolution consistency.

## Approach
Added the missing elementary-weight cons bridge:
`elementaryWeight_node_cons`, plus `elementaryWeight_node_nil` so the new simp rule
does not leave old singleton goals with a stray empty-node factor.

Added the stagewise root-preserving cut sum `cutAt`, proved its leaf and empty-node
computations, then avoided the brittle direct powerset cons proof by factoring the
argument into two smaller invariants:

1. `innerCutForest_sum_foldr_eq`: the list of inner-cut forest choices collapses to a
   `foldr` product of per-child cut/keep factors
   `α child + ∑ j, A i j * cutAt child j`.
2. `foldr_mul_add_eq_powerset_sum_stage`: the `foldr` product expands to the
   powerset sum, after which the child IH rewrites each `cutAt` to `convAt`.

This closes `innerCutForest_stage_sum_eq`, then `cutAt_eq_convAt`. The stage-summed
identity is proved separately by rewriting the option-valued inner-cut list to a
zero-for-`none` list sum and commuting the finite stage sum across the list sum.

## Result
SUCCESS.

Landed:
- `ButcherTableau.cutAt`
- `cutAt_leaf`
- `cutAt_node_nil`
- `cutAt_eq_convAt`
- `bSeriesConv_eq_b_weighted_convAt`
- `ButcherProduct.bSeriesConv_consistency`

Verification completed:
- `lake env lean OpenMath/OrderConditions.lean`
- `lake env lean OpenMath/ButcherGroup/Section386Conv.lean`
- `lake build OpenMath.ButcherGroup.Section386Conv`
- `lake env lean OpenMath/ButcherGroup.lean`
- Lean LSP verification of `ButcherTableau.ButcherProduct.bSeriesConv_consistency`
  and `ButcherTableau.cutAt_eq_convAt`

No tracked `OpenMath/` sorries were introduced.

## Dead ends
The exact direct cons proof requested by the plan is still a poor shape for Lean:
rewriting the kept-head branch inside `flatMap` exposes too much list plumbing at
once. The successful route first proves the `innerCutForest`-to-`foldr` invariant,
then applies a generic powerset expansion.

Aristotle:
- Submitted `Cycle571_EWNodeCons.lean`: `56ded55c-0e3c-480e-a0b8-aae7cc87e01c`
- Submitted `Cycle571_InnerCutForestStage.lean`: `f0006695-9dca-4185-a6e1-22a6a661da8b`
- Third submission hit HTTP 429, so the remaining three jobs were not retried per
  the cycle instruction.
- Final statuses after the 30-minute wait: both accepted jobs were still `QUEUED`.

## Discovery
Making `elementaryWeight_node_cons` a simp lemma requires the companion
`elementaryWeight_node_nil`; otherwise existing singleton-node simplifications
rewrite to `elementaryWeight (node []) i * ...` and stop.

The robust general proof is:

`innerCut` list enumeration
→ root-preserving forest sum
→ `foldr` of child cut/keep factors
→ powerset expansion
→ child IH from `cutAt_eq_convAt`.

This is more modular than the cycle-570 direct node induction and keeps the
elementary-weight cons factorization localized to the kept-child branch.

## Suggested next approach
Use `ButcherProduct.bSeriesConv_consistency` to resume the §384 →
`IsG1Equiv.product_congr` → `G1.mul` chain. The new `cutAt_eq_convAt` theorem is
also the right bridge if later §386 lemmas need stagewise convolution rather than
only the b-weighted statement.
