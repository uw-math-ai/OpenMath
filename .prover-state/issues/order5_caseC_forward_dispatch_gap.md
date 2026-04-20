# Issue: Forward Case C dispatcher gap in `thm_301A_order5`

## Blocker
The forward Case C branches of `thm_301A_order5` cannot yet be routed through the existing shared dispatcher

- `satisfiesTreeCondition_order_five_caseC`

because the forward direction needs a branch-selected target proposition (`order5c` / `order5d` / `order5f`) indexed by `OrderFiveCaseCWitness`, and Lean rejects that packaging with a Prop-elimination restriction.

## Context
Target branches:

- `order5c` for `t5e = [t2, t2]`
- `order5d` for `t5c = [.leaf, t3a]`
- `order5f` for `t5d = [.leaf, t3b]`

Existing dispatcher used:

- `OrderFiveCaseCWitness`
- `order_five_caseC_witness`
- `satisfiesTreeCondition_order_five_caseC`

What was attempted:

- define a shared forward/reverse dispatcher that takes `hwit : OrderFiveCaseCWitness c₁ c₂`,
- package a theorem target selected by the witness branch,
- use that theorem to derive the forward `order5c` / `order5d` / `order5f` branches from the concrete tree hypothesis.

Lean rejected the witness-indexed target packaging with `nested.lean.propRecLargeElim`.

## What was tried
Tried two versions of the shared helper:

1. a theorem returning a `match hwit with ...` target proposition,
2. a helper using a separate `order_five_caseC_target` proposition indexed by `OrderFiveCaseCWitness`.

Both approaches ran into the same issue: selecting the forward theorem target by case analysis on the Prop-indexed witness was not accepted by Lean.

## Possible solutions
Use one of these approaches:

1. replace the witness-indexed target with a non-dependent target encoding that packages the three Case C branches without matching on a Prop witness in the codomain,
2. refactor the Case C witness so the forward target can be selected without Prop elimination,
3. add a forward-only shared wrapper theorem that takes explicit branch data in a non-dependent form and then dispatches to `order5c` / `order5d` / `order5f`.
