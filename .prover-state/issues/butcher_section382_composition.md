# Issue: Butcher §382 raw tableau composition is not associative

## Blocker
The cycle-495 four-parameter composition law
`ButcherProduct : ButcherTableau s -> ButcherTableau t -> ButcherTableau (s + t)`
does not give an associative operation at the raw-tableau level. The intended
construction concatenates stages, scales the nested block, and offsets the
outer block, but nesting changes the weight pattern: `(t1 o t2) o t3`
produces `[gamma1 delta1, gamma1 delta2, gamma2]`, while
`t1 o (t2 o t3)` produces `[gamma1, gamma2 delta1, gamma2 delta2]`.

## Context
The §381 relabel-equivalence relation `IsRKEquivalent` and quotient
`QuotEquiv s` are in place. The §383 invariance lemmas
`elementaryWeight_eq`, `satisfiesTreeCondition_iff`, and `hasTreeOrder_iff`
are also in place, along with the quotient-facing order-condition and sanity
sum lifts. The §387 identity tableau `trivialTableau` has landed.

Composition is the gating piece for the rest of §38: §387 inverse and integer
power need a composition law, and §384 needs a product compatible with the
tree elementary-weight homomorphism.

## What was tried
Cycle 495 attempted the raw four-parameter `ButcherProduct` route and was
reverted after it raised the sorry count from 0 to 1. The recorded task-result
mismatch was exactly the nested weight-list disagreement above.

## Possible solutions
1. Define composition modulo a stage-relabeling equivalence on the sum: land
   `ButcherProduct` and prove `butcherProduct_assoc_modEquiv` on
   `QuotEquiv (s + t + u)`. The reassociation of stages should be a relabel
   of `Fin (s + t + u)`, so the existing invariance layer can cover
   well-definedness on `QuotEquiv`.
2. Route composition through the `G1` tree-elementary-weight homomorphism, as
   in Butcher §384. The B-series side uses convolution on rooted trees, which
   is associative by construction; the remaining question is whether every
   product lifts back to a tableau modulo equivalence.
