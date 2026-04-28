# Cycle 526 Results

## Worked on

Butcher §384 coefficient-parametric `b`-weighted right-block auxiliary,
generalizing the singleton-node form (cycle 525) to arbitrary
`node children`. Added two theorems in `OpenMath/ButcherGroup.lean`:

- `ButcherProduct.rightAuxAtCoef_node_eq_powerset_sum` — unweighted
  powerset-form unfolding of `rightAuxAtCoef t₂ coef (BTree.node children) i`,
  mirroring cycle 521's `rightAuxAt_node_eq_powerset_sum` with `coef`
  replacing `t₁.bSeries`.
- `ButcherProduct.bWeighted_rightAuxAtCoef_node` — the
  `b`-weighted closed form, mirror of cycle 521's
  `bSeries_natAdd_node_eq_powerset_sum`.

## Approach

Followed the strategy's two-step plan: first land the unweighted
identity, then derive the `b`-weighted form from it.

1. **Unweighted form.** `ButcherProduct.rightAuxAtCoef_node` already
   produces the powerset-form sum, so the only gap to the universal
   `Finset (Fin children.length)` indexing was `Finset.powerset_univ`.
   The proof reduces to two rewrites: `rightAuxAtCoef_node` followed by
   `Finset.powerset_univ`. After the rewrites the canonical form
   `∑ S, ...` is definitionally `∑ S ∈ Finset.univ, ...`, so no
   trailing `rfl` is needed (an initial `rfl` raised "no goals").
2. **`b`-weighted form.** Transplanted cycle 521's proof template
   verbatim, with `coef` instead of `t₁.bSeries` and the unweighted
   theorem above as the per-stage substitution. Same `cut`/`keep`
   abbreviations, same five-step `calc` chain:
   `rw [hstage]` → `simp_rw [Finset.mul_sum]` → `Finset.sum_comm` →
   per-`S` `Finset.mul_sum` + `ring` → `simp [cut, keep]`.

## Result

SUCCESS — Both headline theorems landed sorry-free, no stretch goals
attempted (the manual proof closed quickly so no Aristotle batch was
needed).

Verification:
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean`
  succeeded with no output.
- `rg -n "\bsorry\b" OpenMath/ButcherGroup.lean` returned no matches.
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.ButcherGroup`
  succeeded (8029/8029), only pre-existing `OpenMath.OrderConditions`
  `ring`/`ring_nf` infos.

`plan.md` updated under both the §384 ledger and the `## Current Target`
paragraph. §38 stays as Current Target; backlog rotation deferred.

## Aristotle status

Did not submit this cycle. The strategy's Aristotle policy capped usage
at one batch only if the powerset rewrite stalled past 15–20 minutes of
manual work. The cycle 521 template transplanted directly: the
unweighted identity closed in two rewrites, and the `b`-weighted form
closed with the verbatim cycle 521 calc chain. No batch needed.

## Dead ends

Initial draft of `rightAuxAtCoef_node_eq_powerset_sum` ended with a
trailing `rfl` after `rw [Finset.powerset_univ]`. Lean rejected it with
"No goals to be solved" because `Finset.powerset_univ` already produces
the canonical universal-Finset form. Removed the `rfl`; proof closes in
the two rewrites alone.

## Discovery

`Finset.powerset_univ` is the right rewrite to bridge between
`rightAuxAtCoef_node`'s `S ∈ Finset.univ.powerset` indexing and the
canonical `∑ S : Finset (Fin n), ...` form used downstream. This avoids
the `Finset.compl_eq_univ_sdiff` + `Equiv.sum_comp` dance cycle 521 used
on the `rightAuxAt` side, because `rightAuxAtCoef`'s defining equation
already writes the cut product over `Sᶜ` and the kept product over `S`.
This makes the coefficient-parametric form a strictly simpler powerset
identity than the cycle 521 mirror.

## Suggested next approach

Mirror cycle 522's two-level expansion: prove
`ButcherProduct.rightAuxAtCoef_node_two_level_eq_powerset_sum` and its
`b`-weighted form, case-splitting each kept child via `BTree.cases` /
`generalize children.get p = c`. Leaf children contribute
`∑ j, t₂.A i j`; node children unfold into the inner powerset sum at
the new parent index. After that, the §384 convolution should close as
a corollary by specializing `coef = t₁.bSeries` and stitching the
cycle 524 structural equivalence into the existing
`bSeries_natAdd_eq_rightAuxAtCoef` corollary.
