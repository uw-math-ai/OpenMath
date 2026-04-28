# Cycle 525 Results

## Worked on

Butcher §384 coefficient-parametric `b`-weighted right-block reductions in
`OpenMath/ButcherGroup.lean`.

Added:
- `ButcherTableau.weightsSum`
- `ButcherProduct.bWeighted_rightAuxAtCoef_leaf`
- `ButcherProduct.rightAuxAtCoef_node_singleton`
- `ButcherProduct.bWeighted_rightAuxAtCoef_node_singleton`

## Approach

1. Followed the sorry-first surface from the strategy: added the three
   theorem statements with `sorry`, then verified the surface with
   `lake env lean OpenMath/ButcherGroup.lean`.
2. Added the raw tableau abbreviation `ButcherTableau.weightsSum` because
   the file only had quotient-level `QuotEquiv.weightsSum`, while the
   planned lemmas are about raw `ButcherTableau` values.
3. Closed the leaf weighted lemma by simplifying
   `rightAuxAtCoef_leaf` and unfolding `ButcherTableau.weightsSum`.
4. Closed the singleton-node lemma by rewriting
   `rightAuxAtCoef_node`, reducing the powerset of `{0 : Fin 1}` to
   `{∅, {0}}`, and simplifying the singleton complement.
5. Closed the weighted singleton form by rewriting each stage with
   `rightAuxAtCoef_node_singleton`, distributing over the finite sum, and
   factoring the constant cut term into `coef child * t₂.weightsSum`.

## Result

SUCCESS — Steps A, B, and C from the cycle strategy landed with no live
`sorry`s.

Verification:
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean`
  succeeded.
- `rg -n "\bsorry\b" OpenMath/ButcherGroup.lean` returned no matches.
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.ButcherGroup`
  succeeded, with only pre-existing `OpenMath.OrderConditions` warning/info
  output.

`plan.md` was updated under the Chapter 3 §384 ledger and the
`## Current Target` body. §38 remains active.

## Aristotle status

Did not submit this cycle. The planner's cycle-525 Aristotle policy capped
usage at one batch only if a sorry-first scaffold actually needed help, and
explicitly said not to spend a batch on goals that close manually. After the
scaffold check, all three target lemmas closed directly with local
simplification, a singleton powerset normalization, and finite-sum algebra.

## Dead ends

The strategy's statement used `t₂.weightsSum`, but the existing file only
defined `weightsSum` for `QuotEquiv`; Lean rejected the raw tableau field
notation. I added the missing raw abbreviation
`ButcherTableau.weightsSum := ∑ i, t.b i`, which makes the intended theorem
surface compile and keeps the result aligned with the quotient-facing API.

A bare `simp [ButcherProduct.rightAuxAtCoef_node]` for the singleton node
left a powerset/cardinality normal form over `{0 : Fin 1}`. The proof now
records the finite powerset identity and the complement identity explicitly.

## Discovery

For `node [child]`, the closed auxiliary reduces to the two subsets of
`Fin 1`: cutting the child contributes `coef child`, while keeping it
contributes the `A`-twisted recursive sum. This gives a small, reusable
witness of the cut/keep branching before attempting the general
`node children` powerset form.

## Suggested next approach

Generalize the singleton weighted lemma to arbitrary `node children`:
express

```lean
∑ i : Fin t, t₂.b i * rightAuxAtCoef t₂ coef (BTree.node children) i
```

as a powerset-indexed sum over kept children, with cut children contributing
`coef` factors and kept children contributing the `A`-twisted recursive
`rightAuxAtCoef` calls. The proof should mirror
`ButcherProduct.bSeries_natAdd_node_eq_powerset_sum`, but use `coef`
instead of `t₁.bSeries`.
