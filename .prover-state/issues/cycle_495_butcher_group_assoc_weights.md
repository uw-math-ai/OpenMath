# Issue: ButcherProduct associativity weight parameters

## Blocker

The deferred theorem `butcherProduct_assoc_modEquiv` currently follows the
cycle-495 scaffold and compares

```lean
ButcherProduct γ₁ γ₂ (ButcherProduct δ₁ δ₂ t₁ t₂) t₃
```

with

```lean
ButcherProduct γ₁ γ₂ t₁ (ButcherProduct δ₁ δ₂ t₂ t₃)
```

up to a stage permutation.  The stage-count mismatch is handled by a
`Nat.add_assoc` transport, but the weights are not generally associative with
the same four parameters on both nestings.

## Context

For one-stage tableaux, the left-nested product has final weights

```text
[γ₁ * δ₁, γ₁ * δ₂, γ₂]
```

while the right-nested product has final weights

```text
[γ₁, γ₂ * δ₁, γ₂ * δ₂]
```

Stage relabelling can only permute these entries, not change their values.
For generic real parameters the two multisets are different.

## What was tried

Cycle 495 implemented the requested sorry-first theorem with the necessary
`Nat.add_assoc` transport and submitted it to Aristotle as project
`8314c9b0-d74e-41dc-8ff6-4da6f7896a93`.  After the mandated 30-minute wait it
was still `IN_PROGRESS` at 17%, so no proof was incorporated.

The local proofs closed all non-associativity infrastructure:

- `relabel_comp`
- `IsRKEquivalent.refl/symm/trans`
- `butcherProduct_identity_left/right`

## Possible solutions

1. Reparameterize associativity by three actual substep weights
   `α β χ : ℝ`.  The left nesting should use outer weights
   `(α + β, χ)` and inner normalized weights for `t₁/t₂`; the right nesting
   should use outer weights `(α, β + χ)` and inner normalized weights for
   `t₂/t₃`.  This likely requires side conditions for denominators if using
   normalized ratios.
2. Alternatively define an unnormalized ternary product first, prove both
   nestings equal to that product after `Fin` associator reindexing, and then
   derive a normalized statement under the desired hypotheses.
3. If the intended Butcher §38 product uses group coefficients rather than
   literal step-size fractions, revise `ButcherProduct` or the theorem
   statement before attempting the `Equiv.sumAssoc` proof.
